use {
    crate::{
        analyzing::{private_recursion::PrivateRecursion, tightness::Tightness},
        breaking::fol::ht::break_equivalences_annotated_formula,
        command_line::arguments::{Decomposition, FormulaRepresentation},
        convenience::{
            apply::Apply as _,
            compose::Compose as _,
            with_warnings::{Result, WithWarnings},
        },
        simplifying::fol::{classic::CLASSIC, ht::HT, intuitionistic::INTUITIONISTIC},
        syntax_tree::{asp, fol},
        translating::{completion::completion, tau_star::tau_star},
        verifying::{
            outline::{
                CheckInternal, GeneralLemma, ProofOutline, ProofOutlineError, ProofOutlineWarning,
            },
            problem::{self, Problem},
            task::Task,
        },
    },
    either::Either,
    indexmap::{IndexMap, IndexSet},
    std::fmt::Display,
    thiserror::Error,
};

trait RenamePredicates {
    fn rename_predicates(self, mapping: &IndexMap<fol::Predicate, String>) -> Self;
}

impl RenamePredicates for fol::Specification {
    fn rename_predicates(self, mapping: &IndexMap<fol::Predicate, String>) -> Self {
        fol::Specification {
            formulas: self
                .formulas
                .into_iter()
                .map(|f| f.rename_predicates(mapping))
                .collect(),
        }
    }
}

impl RenamePredicates for fol::AnnotatedFormula {
    fn rename_predicates(mut self, mapping: &IndexMap<fol::Predicate, String>) -> Self {
        self.formula = self.formula.rename_predicates(mapping);
        self
    }
}

impl RenamePredicates for fol::Formula {
    fn rename_predicates(self, mapping: &IndexMap<fol::Predicate, String>) -> Self {
        self.apply(&mut |formula| match formula {
            fol::Formula::AtomicFormula(a) => {
                fol::Formula::AtomicFormula(a.rename_predicates(mapping))
            }
            x => x,
        })
    }
}

impl RenamePredicates for fol::AtomicFormula {
    fn rename_predicates(self, mapping: &IndexMap<fol::Predicate, String>) -> Self {
        match self {
            fol::AtomicFormula::Atom(a) => fol::AtomicFormula::Atom(a.rename_predicates(mapping)),
            x => x,
        }
    }
}

impl RenamePredicates for fol::Atom {
    fn rename_predicates(self, mapping: &IndexMap<fol::Predicate, String>) -> Self {
        match mapping.get(&self.predicate()) {
            Some(name_extension) => fol::Atom {
                predicate_symbol: format!("{}_{}", self.predicate_symbol, name_extension),
                terms: self.terms,
            },
            None => self,
        }
    }
}

#[derive(Clone, Debug)]
struct DefinitionSequenceNode {
    lhs: fol::Predicate,
    rhs: IndexSet<fol::Predicate>,
}

#[derive(Clone, Debug)]
struct DefinitionSequence {
    nodes: Vec<DefinitionSequenceNode>,
    base_predicates: IndexSet<fol::Predicate>,
}

impl DefinitionSequence {
    fn previously_defined_predicates(&self, index: usize) -> IndexSet<fol::Predicate> {
        if index == 0 {
            self.base_predicates.clone()
        } else {
            let parent = self.nodes[index - 1].clone();
            let mut previous = self.previously_defined_predicates(index - 1);
            previous.insert(parent.lhs);
            previous
        }
    }

    fn index(&self, p: &fol::Predicate) -> Option<i64> {
        if self.base_predicates.contains(p) {
            return Some(-1);
        }

        for (i, predicate) in self.nodes.iter().enumerate() {
            if predicate.lhs == *p {
                let index: i64 = i.try_into().unwrap();
                return Some(index);
            }
        }

        None
    }
}

#[derive(Error, Debug)]
pub enum ExternalEquivalenceTaskWarning {
    NonTightProgram(asp::Program),
    InconsistentDirectionAnnotation(fol::AnnotatedFormula),
    InvalidRoleWithinUserGuide(fol::AnnotatedFormula),
    DefinitionWithWarning(#[from] ProofOutlineWarning),
}

impl Display for ExternalEquivalenceTaskWarning {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ExternalEquivalenceTaskWarning::NonTightProgram(program) => {
                writeln!(f, "the following program is not tight: ")?;
                writeln!(f, "{program}")
            }
            ExternalEquivalenceTaskWarning::InconsistentDirectionAnnotation(formula) => {
                let proof_direction = match formula.direction {
                    fol::Direction::Forward => fol::Direction::Backward,
                    fol::Direction::Backward => fol::Direction::Forward,
                    fol::Direction::Universal => unreachable!(),
                };

                writeln!(
                    f,
                    "the following assumption is ignored in the {proof_direction} direction of the proof due its annotated direction: {formula}"
                )
            }
            ExternalEquivalenceTaskWarning::InvalidRoleWithinUserGuide(formula) => writeln!(
                f,
                "the following formula is ignored because user guides only permit assumptions: {formula}"
            ),
            ExternalEquivalenceTaskWarning::DefinitionWithWarning(w) => writeln!(f, "{w}"),
        }
    }
}

#[derive(Debug)]
pub struct InvalidPredicateErrorContent {
    pub formula: fol::AnnotatedFormula,
    pub predicate: fol::Predicate,
}

#[derive(Error, Debug)]
pub enum ExternalEquivalenceTaskError {
    UnsupportedFormulaRepresentation,
    NonTightProgram(asp::Program),
    ProgramContainsPrivateRecursion(asp::Program),
    InputOutputPredicatesOverlap(Vec<fol::Predicate>),
    InputPredicateInRuleHead(Vec<fol::Predicate>),
    OutputPredicateInUserGuideAssumption(Vec<fol::Predicate>),
    OutputPredicateInSpecificationAssumption(Vec<fol::Predicate>),
    PlaceholdersWithIdenticalNamesDifferentSorts(String),
    AssumptionContainsInvalidPredicate(Box<InvalidPredicateErrorContent>),
    SpecContainsInvalidPredicate(Box<InvalidPredicateErrorContent>),
    AssumptionContainsNonInputSymbols(fol::AnnotatedFormula),
    SpecificationContainsUnsupportedRoles(fol::AnnotatedFormula),
    SpecificationDefinesOutputPredicates(Vec<fol::Predicate>),
    ProofOutlineError(#[from] ProofOutlineError),
}

impl Display for ExternalEquivalenceTaskError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ExternalEquivalenceTaskError::NonTightProgram(program) => {
                writeln!(f, "the following program is not tight: ")?;
                writeln!(f, "{program}")
            }
            ExternalEquivalenceTaskError::ProgramContainsPrivateRecursion(program) => {
                writeln!(f, "the following program contains private recursion: ")?;
                writeln!(f, "{program}")
            }
            ExternalEquivalenceTaskError::InputOutputPredicatesOverlap(predicates) => {
                write!(
                    f,
                    "the following predicates are declared as input and output predicates: "
                )?;

                let mut iter = predicates.iter().peekable();
                for predicate in predicates {
                    write!(f, "{predicate}")?;
                    if iter.peek().is_some() {
                        write!(f, ", ")?;
                    }
                }

                writeln!(f)
            }
            ExternalEquivalenceTaskError::InputPredicateInRuleHead(predicates) => {
                write!(f, "the following input predicates occur in rule heads: ")?;

                let mut iter = predicates.iter().peekable();
                for predicate in predicates {
                    write!(f, "{predicate}")?;
                    if iter.peek().is_some() {
                        write!(f, ", ")?;
                    }
                }

                writeln!(f)
            }
            ExternalEquivalenceTaskError::OutputPredicateInUserGuideAssumption(predicates) => {
                write!(
                    f,
                    "the following output predicates occur in user guide assumptions: "
                )?;

                let mut iter = predicates.iter().peekable();
                for predicate in predicates {
                    write!(f, "{predicate}")?;
                    if iter.peek().is_some() {
                        write!(f, ", ")?;
                    }
                }

                writeln!(f)
            }
            ExternalEquivalenceTaskError::OutputPredicateInSpecificationAssumption(predicates) => {
                write!(
                    f,
                    "the following output predicates occur in specification assumptions: "
                )?;

                let mut iter = predicates.iter().peekable();
                for predicate in predicates {
                    write!(f, "{predicate}")?;
                    if iter.peek().is_some() {
                        write!(f, ", ")?;
                    }
                }

                writeln!(f)
            }
            ExternalEquivalenceTaskError::PlaceholdersWithIdenticalNamesDifferentSorts(s) => {
                writeln!(
                    f,
                    "the following placeholder is given conflicting sorts within the user guide: {s}"
                )
            }
            ExternalEquivalenceTaskError::AssumptionContainsInvalidPredicate(content) => {
                let content = &**content;
                let predicate = &content.predicate;
                let formula = &content.formula;
                writeln!(
                    f,
                    "the following assumption contains a predicate ({predicate}) that is not valid for use within assumptions: {formula}"
                )
            }
            ExternalEquivalenceTaskError::SpecContainsInvalidPredicate(content) => {
                let content = &**content;
                let predicate = &content.predicate;
                let formula = &content.formula;
                writeln!(
                    f,
                    "the following spec contains a predicate ({predicate}) that is not valid for use within specs: {formula}"
                )
            }
            ExternalEquivalenceTaskError::ProofOutlineError(_) => {
                writeln!(f, "a definition or lemma contains errors")
            }
            ExternalEquivalenceTaskError::UnsupportedFormulaRepresentation => {
                writeln!(
                    f,
                    "tau-star is the only formula-representation currently supported for external equivalence"
                )
            }
            ExternalEquivalenceTaskError::SpecificationContainsUnsupportedRoles(formula) => {
                writeln!(
                    f,
                    "the role of the following formula is not supported in specifications: {formula}"
                )
            }
            ExternalEquivalenceTaskError::SpecificationDefinesOutputPredicates(predicates) => {
                write!(
                    f,
                    "the specification defines the following output predicates: "
                )?;

                let mut iter = predicates.iter().peekable();
                for predicate in predicates {
                    write!(f, "{predicate}")?;
                    if iter.peek().is_some() {
                        write!(f, ", ")?;
                    }
                }

                writeln!(f)
            }
        }
    }
}

// A predicate is valid for use in a (spec or assumption) based on a valid sequence if
// 1. it occurs in the set of base predicates or
// 2. it is defined in the sequence and the RHS contains only previously defined predicates and each ancestor is valid.
fn valid(sequence: &DefinitionSequence, p: fol::Predicate) -> bool {
    match sequence.index(&p) {
        Some(index) => {
            if index == -1 {
                true
            } else {
                let index: usize = index.try_into().unwrap();
                let node = sequence.nodes[index].clone();
                let pdp = sequence.previously_defined_predicates(index);
                if node.rhs.difference(&pdp).next().is_some() {
                    false
                } else if index == 0 {
                    true
                } else {
                    let parent = sequence.nodes[index - 1].clone();
                    valid(sequence, parent.lhs)
                }
            }
        }
        None => false,
    }
}

#[derive(Debug)]
pub struct ExternalEquivalenceTask {
    pub specification: Either<asp::Program, fol::Specification>,
    pub program: asp::Program,
    pub user_guide: fol::UserGuide,
    pub proof_outline: fol::Specification,
    pub decomposition: Decomposition,
    pub direction: fol::Direction,
    pub formula_representation: FormulaRepresentation,
    pub bypass_tightness: bool,
    pub simplify: bool,
    pub break_equivalences: bool,
}

impl ExternalEquivalenceTask {
    fn ensure_program_tightness(
        &self,
        program: &asp::Program,
    ) -> Result<(), ExternalEquivalenceTaskWarning, ExternalEquivalenceTaskError> {
        if program.is_tight() {
            Ok(WithWarnings::flawless(()))
        } else if self.bypass_tightness {
            Ok(WithWarnings::flawless(()).add_warning(
                ExternalEquivalenceTaskWarning::NonTightProgram(program.clone()),
            ))
        } else {
            Err(ExternalEquivalenceTaskError::NonTightProgram(
                program.clone(),
            ))
        }
    }

    fn ensure_absence_of_private_recursion(
        &self,
        program: &asp::Program,
        private_predicates: &IndexSet<fol::Predicate>,
    ) -> Result<(), ExternalEquivalenceTaskWarning, ExternalEquivalenceTaskError> {
        let private_predicates = private_predicates
            .into_iter()
            .cloned()
            .map(asp::Predicate::from)
            .collect();

        if program.has_private_recursion(&private_predicates) {
            Err(ExternalEquivalenceTaskError::ProgramContainsPrivateRecursion(program.clone()))
        } else {
            Ok(WithWarnings::flawless(()))
        }
    }

    fn ensure_input_and_output_predicates_are_disjoint(
        &self,
    ) -> Result<(), ExternalEquivalenceTaskWarning, ExternalEquivalenceTaskError> {
        let input_predicates = self.user_guide.input_predicates();
        let output_predicates = self.user_guide.output_predicates();

        let intersection: Vec<_> = input_predicates
            .intersection(&output_predicates)
            .cloned()
            .collect();

        if intersection.is_empty() {
            Ok(WithWarnings::flawless(()))
        } else {
            Err(ExternalEquivalenceTaskError::InputOutputPredicatesOverlap(
                intersection,
            ))
        }
    }

    fn ensure_rule_heads_do_not_contain_input_predicates(
        &self,
        program: &asp::Program,
    ) -> Result<(), ExternalEquivalenceTaskWarning, ExternalEquivalenceTaskError> {
        let input_predicates = self.user_guide.input_predicates();
        let head_predicates: IndexSet<_> = program
            .head_predicates()
            .into_iter()
            .map(fol::Predicate::from)
            .collect();

        let intersection: Vec<_> = input_predicates
            .intersection(&head_predicates)
            .cloned()
            .collect();

        if intersection.is_empty() {
            Ok(WithWarnings::flawless(()))
        } else {
            Err(ExternalEquivalenceTaskError::InputPredicateInRuleHead(
                intersection,
            ))
        }
    }

    fn ensure_specification_assumptions_do_not_contain_output_predicates(
        &self,
        specification: &fol::Specification,
    ) -> Result<(), ExternalEquivalenceTaskWarning, ExternalEquivalenceTaskError> {
        let output_predicates = self.user_guide.output_predicates();

        for formula in &specification.formulas {
            if matches!(formula.role, fol::Role::Assumption) {
                let overlap: Vec<_> = formula
                    .predicates()
                    .into_iter()
                    .filter(|p| output_predicates.contains(p))
                    .collect();

                if !overlap.is_empty() {
                    return Err(
                        ExternalEquivalenceTaskError::OutputPredicateInSpecificationAssumption(
                            overlap,
                        ),
                    );
                }
            }
        }

        Ok(WithWarnings::flawless(()))
    }

    fn ensure_placeholder_name_uniqueness(
        &self,
    ) -> Result<(), ExternalEquivalenceTaskWarning, ExternalEquivalenceTaskError> {
        let placeholders = self.user_guide.placeholders();
        let mut names = IndexSet::new();
        for p in placeholders {
            if names.contains(&p.name) {
                return Err(
                    ExternalEquivalenceTaskError::PlaceholdersWithIdenticalNamesDifferentSorts(
                        p.name,
                    ),
                );
            } else {
                names.insert(p.name);
            }
        }

        Ok(WithWarnings::flawless(()))
    }

    fn ensure_assumptions_only_contain_valid_predicates(
        &self,
        formulas: &Vec<fol::AnnotatedFormula>,
    ) -> Result<(), ExternalEquivalenceTaskWarning, ExternalEquivalenceTaskError> {
        let base_predicates = self.user_guide.input_predicates();
        let sequence =
            ensure_valid_definition_sequence(formulas, &self.user_guide, base_predicates)?;

        for formula in formulas {
            if matches!(formula.role, fol::Role::Assumption) {
                for p in formula.formula.predicates() {
                    if !valid(&sequence.data, p.clone()) {
                        return Err(
                            ExternalEquivalenceTaskError::AssumptionContainsInvalidPredicate(
                                Box::new(InvalidPredicateErrorContent {
                                    formula: formula.clone(),
                                    predicate: p,
                                }),
                            ),
                        );
                    }
                }
            }
        }

        Ok(WithWarnings::flawless(()).preface_warnings(sequence.warnings))
    }

    fn ensure_specs_only_contain_valid_predicates(
        &self,
        formulas: &Vec<fol::AnnotatedFormula>,
    ) -> Result<(), ExternalEquivalenceTaskWarning, ExternalEquivalenceTaskError> {
        // TODO: should output predicates be allowed in the set of base predicates?
        // let base_predicates = self.user_guide.public_predicates();
        let base_predicates = self.user_guide.input_predicates();
        let sequence =
            ensure_valid_definition_sequence(formulas, &self.user_guide, base_predicates)?;

        for formula in formulas {
            if matches!(formula.role, fol::Role::Assumption) {
                for p in formula.formula.predicates() {
                    if !valid(&sequence.data, p.clone()) {
                        return Err(ExternalEquivalenceTaskError::SpecContainsInvalidPredicate(
                            Box::new(InvalidPredicateErrorContent {
                                formula: formula.clone(),
                                predicate: p,
                            }),
                        ));
                    }
                }
            }
        }

        Ok(WithWarnings::flawless(()).preface_warnings(sequence.warnings))
    }

    fn ensure_user_guide_assumptions_only_contain_input_symbols(
        &self,
        formulas: &Vec<fol::AnnotatedFormula>,
    ) -> Result<(), ExternalEquivalenceTaskWarning, ExternalEquivalenceTaskError> {
        for formula in formulas {
            if matches!(formula.role, fol::Role::Assumption) {
                let predicates = formula.formula.predicates();
                if predicates
                    .difference(&self.user_guide.input_predicates())
                    .next()
                    .is_some()
                {
                    return Err(
                        ExternalEquivalenceTaskError::AssumptionContainsNonInputSymbols(
                            formula.clone(),
                        ),
                    );
                }
            }
        }

        Ok(WithWarnings::flawless(()))
    }

    fn ensure_valid_formula_representation(
        &self,
    ) -> Result<(), ExternalEquivalenceTaskWarning, ExternalEquivalenceTaskError> {
        if !matches!(self.formula_representation, FormulaRepresentation::TauStar) {
            return Err(ExternalEquivalenceTaskError::UnsupportedFormulaRepresentation);
        }

        Ok(WithWarnings::flawless(()))
    }

    fn ensure_specification_roles_are_supported(
        &self,
        formulas: &Vec<fol::AnnotatedFormula>,
    ) -> Result<(), ExternalEquivalenceTaskWarning, ExternalEquivalenceTaskError> {
        for formula in formulas {
            if !(matches!(
                formula.role,
                fol::Role::Assumption | fol::Role::Spec | fol::Role::Definition
            )) {
                return Err(
                    ExternalEquivalenceTaskError::SpecificationContainsUnsupportedRoles(
                        formula.clone(),
                    ),
                );
            }
        }

        Ok(WithWarnings::flawless(()))
    }

    fn ensure_valid_definition_sequence(
        specification: &Vec<fol::AnnotatedFormula>,
        user_guide: &fol::UserGuide,
        base_predicates: IndexSet<fol::Predicate>,
    ) -> Result<DefinitionSequence, ExternalEquivalenceTaskWarning, ExternalEquivalenceTaskError>
    {
        let mut warnings = Vec::new();
        let mut nodes = Vec::new();

        let mut taken_predicates = base_predicates.clone();
        for anf in specification {
            if matches!(anf.role, fol::Role::Definition) {
                let predicate = anf.formula.definition(&taken_predicates)?;
                warnings.extend(predicate.warnings);

                let p = predicate.data;
                taken_predicates.insert(p.clone());

                let rhs = anf.formula.definition_rhs()?;
                warnings.extend(rhs.warnings);
                nodes.push(DefinitionSequenceNode {
                    lhs: p,
                    rhs: rhs.data.predicates(),
                });
            }
        }

        // check for no overlap with output predicates
        let output_predicates = user_guide.output_predicates();
        let overlap: Vec<_> = taken_predicates
            .into_iter()
            .filter(|p| output_predicates.contains(p))
            .collect();
        if !overlap.is_empty() {
            return Err(
                ExternalEquivalenceTaskError::SpecificationDefinesOutputPredicates(overlap),
            );
        }

        Ok(WithWarnings::flawless(DefinitionSequence {
            nodes,
            base_predicates,
        }))
    }
}

impl Task for ExternalEquivalenceTask {
    type Error = ExternalEquivalenceTaskError;
    type Warning = ExternalEquivalenceTaskWarning;

    fn decompose(self) -> Result<Vec<Problem>, Self::Warning, Self::Error> {
        self.ensure_valid_formula_representation()?;

        let placeholders = self
            .user_guide
            .placeholders()
            .into_iter()
            .map(|p| (p.name.clone(), p))
            .collect();

        let public_predicates = self.user_guide.public_predicates();

        let specification_private_predicates: IndexSet<_> = match self.specification {
            Either::Left(ref program) => program
                .predicates()
                .into_iter()
                .map(fol::Predicate::from)
                .filter(|p| !public_predicates.contains(p))
                .collect(),
            Either::Right(ref specification) => specification
                .predicates()
                .into_iter()
                .filter(|p| !public_predicates.contains(p))
                .collect(),
        };

        let program_private_predicates: IndexSet<_> = self
            .program
            .predicates()
            .into_iter()
            .map(fol::Predicate::from)
            .filter(|p| !public_predicates.contains(p))
            .collect();

        let mut warnings = Vec::new();

        self.ensure_input_and_output_predicates_are_disjoint()?;
        warnings.extend(self.ensure_program_tightness(&self.program)?.warnings);
        self.ensure_absence_of_private_recursion(&self.program, &program_private_predicates)?;
        self.ensure_rule_heads_do_not_contain_input_predicates(&self.program)?;
        self.ensure_placeholder_name_uniqueness()?;
        self.ensure_user_guide_assumptions_only_contain_input_symbols(&self.user_guide.formulas())?;

        match self.specification {
            Either::Left(ref program) => {
                warnings.extend(self.ensure_program_tightness(program)?.warnings);
                self.ensure_absence_of_private_recursion(
                    program,
                    &specification_private_predicates,
                )?;
                self.ensure_rule_heads_do_not_contain_input_predicates(program)?;
            }
            Either::Right(ref specification) => {
                self.ensure_specification_assumptions_do_not_contain_output_predicates(
                    specification,
                )?;
                self.ensure_assumptions_only_contain_valid_predicates(&specification.formulas)?;
                self.ensure_specification_roles_are_supported(&specification.formulas)?;
                self.ensure_specs_only_contain_valid_predicates(&specification.formulas)?;
            }
        }

        fn head_predicate(formula: &fol::Formula) -> Option<fol::Predicate> {
            match formula {
                fol::Formula::BinaryFormula {
                    connective: fol::BinaryConnective::Equivalence,
                    lhs,
                    rhs: _,
                } => match **lhs {
                    fol::Formula::AtomicFormula(fol::AtomicFormula::Atom(ref a)) => {
                        Some(a.predicate())
                    }
                    _ => None,
                },
                fol::Formula::QuantifiedFormula {
                    quantification:
                        fol::Quantification {
                            quantifier: fol::Quantifier::Forall,
                            variables: _,
                        },
                    formula,
                } => head_predicate(formula),
                _ => None,
            }
        }

        let theory_translate = |program: asp::Program| {
            // TODO: allow more formula representations beyond tau-star
            let mut theory = completion(
                tau_star(program).replace_placeholders(&placeholders),
                self.user_guide.input_predicates(),
            )
            .expect("tau_star did not create a completable theory");

            if self.simplify {
                let mut portfolio = [INTUITIONISTIC, HT, CLASSIC].concat().into_iter().compose();
                theory = theory
                    .into_iter()
                    .map(|f| f.apply_fixpoint(&mut portfolio))
                    .collect();
            }

            theory
        };

        let control_translate = |theory: fol::Theory| {
            let mut constraint_counter = 0..;
            let formulas = theory
                .formulas
                .into_iter()
                .map(|formula| match head_predicate(&formula) {
                    Some(p) if public_predicates.contains(&p) => fol::AnnotatedFormula {
                        role: fol::Role::Spec,
                        direction: fol::Direction::Universal,
                        name: format!("completed_definition_of_{}_{}", p.symbol, p.arity),
                        formula,
                    },
                    Some(p) => fol::AnnotatedFormula {
                        role: fol::Role::Assumption,
                        direction: fol::Direction::Universal,
                        name: format!("completed_definition_of_{}_{}", p.symbol, p.arity),
                        formula,
                    },
                    None => fol::AnnotatedFormula {
                        role: fol::Role::Spec,
                        direction: fol::Direction::Universal,
                        name: format!("constraint_{}", constraint_counter.next().unwrap()),
                        formula,
                    },
                })
                .collect();
            fol::Specification { formulas }
        };

        let left = match self.specification {
            Either::Left(program) => control_translate(theory_translate(program)),
            Either::Right(specification) => specification.replace_placeholders(&placeholders),
        };

        let right = control_translate(theory_translate(self.program));

        // TODO: Warn when a conflict between private predicates is encountered
        // TODO: Check if renaming creates new conflicts
        let right = right.rename_predicates(
            &specification_private_predicates
                .intersection(&program_private_predicates)
                .map(|p| (p.clone(), "p".to_string()))
                .collect(),
        );

        let mut user_guide_assumptions = Vec::new();
        for formula in self.user_guide.formulas() {
            match formula.role {
                fol::Role::Assumption => {
                    let overlap: Vec<_> = formula
                        .predicates()
                        .into_iter()
                        .filter(|p| self.user_guide.output_predicates().contains(p))
                        .collect();
                    if overlap.is_empty() {
                        user_guide_assumptions.push(formula.replace_placeholders(&placeholders));
                    } else {
                        return Err(
                            ExternalEquivalenceTaskError::OutputPredicateInUserGuideAssumption(
                                overlap,
                            ),
                        );
                    }
                }
                _ => warnings.push(ExternalEquivalenceTaskWarning::InvalidRoleWithinUserGuide(
                    formula,
                )),
            }
        }

        let mut taken_predicates = self.user_guide.input_predicates();
        for anf in left.formulas.iter() {
            taken_predicates.extend(anf.formula.predicates());
        }
        for anf in right.formulas.iter() {
            taken_predicates.extend(anf.formula.predicates());
        }

        let proof_outline_construction =
            ProofOutline::from_specification(self.proof_outline, taken_predicates, &placeholders)?;
        warnings.extend(
            proof_outline_construction
                .warnings
                .into_iter()
                .map(ExternalEquivalenceTaskWarning::from),
        );

        Ok(ValidatedExternalEquivalenceTask {
            left: left.formulas,
            right: right.formulas,
            user_guide_assumptions,
            proof_outline: proof_outline_construction.data,
            decomposition: self.decomposition,
            direction: self.direction,
            break_equivalences: self.break_equivalences,
        }
        .decompose()?
        .preface_warnings(warnings))
    }
}

struct ValidatedExternalEquivalenceTask {
    pub left: Vec<fol::AnnotatedFormula>, // TODO: Use fol::Specification?
    pub right: Vec<fol::AnnotatedFormula>,
    pub user_guide_assumptions: Vec<fol::AnnotatedFormula>,
    pub proof_outline: ProofOutline,
    pub decomposition: Decomposition,
    pub direction: fol::Direction,
    pub break_equivalences: bool,
}

impl Task for ValidatedExternalEquivalenceTask {
    type Error = ExternalEquivalenceTaskError;
    type Warning = ExternalEquivalenceTaskWarning;

    fn decompose(self) -> Result<Vec<Problem>, Self::Warning, Self::Error> {
        use crate::{
            syntax_tree::fol::{Direction::*, Role::*},
            verifying::problem::Role::*,
        };

        let mut stable_premises: Vec<_> = self
            .user_guide_assumptions
            .into_iter()
            .map(|a| a.into_problem_formula(problem::Role::Axiom))
            .collect();

        let mut forward_premises = Vec::new();
        let mut forward_conclusions = Vec::new();
        let mut backward_premises = Vec::new();
        let mut backward_conclusions = Vec::new();

        let mut warnings = Vec::new();

        for formula in self.left {
            match formula.role {
                Assumption | Definition => match formula.direction {
                    Universal => stable_premises.push(formula.into_problem_formula(Axiom)),
                    Forward => forward_premises.push(formula.into_problem_formula(Axiom)),
                    Backward => warnings.push(
                        ExternalEquivalenceTaskWarning::InconsistentDirectionAnnotation(formula),
                    ),
                },
                Spec => {
                    if matches!(formula.direction, Universal | Forward) {
                        forward_premises.push(formula.clone().into_problem_formula(Axiom))
                    }
                    if matches!(formula.direction, Universal | Backward) {
                        if self.break_equivalences {
                            for formula in break_equivalences_annotated_formula(formula) {
                                backward_conclusions.push(formula.into_problem_formula(Conjecture))
                            }
                        } else {
                            backward_conclusions.push(formula.into_problem_formula(Conjecture))
                        }
                    }
                }
                Lemma | InductiveLemma => unreachable!(),
            }
        }

        for formula in self.right {
            match formula.role {
                Assumption => match formula.direction {
                    Universal => stable_premises.push(formula.into_problem_formula(Axiom)),
                    Forward => warnings.push(
                        ExternalEquivalenceTaskWarning::InconsistentDirectionAnnotation(formula),
                    ),
                    Backward => backward_premises.push(formula.into_problem_formula(Axiom)),
                },
                Spec => {
                    if matches!(formula.direction, Universal | Backward) {
                        backward_premises.push(formula.clone().into_problem_formula(Axiom))
                    }
                    if matches!(formula.direction, Universal | Forward) {
                        if self.break_equivalences {
                            for formula in break_equivalences_annotated_formula(formula) {
                                forward_conclusions.push(formula.into_problem_formula(Conjecture))
                            }
                        } else {
                            forward_conclusions.push(formula.into_problem_formula(Conjecture))
                        }
                    }
                }
                Lemma | Definition | InductiveLemma => unreachable!(),
            }
        }

        Ok(AssembledExternalEquivalenceTask {
            stable_premises,
            forward_premises,
            forward_conclusions,
            backward_premises,
            backward_conclusions,
            proof_outline: self.proof_outline,
            decomposition: self.decomposition,
            direction: self.direction,
        }
        .decompose()?
        .preface_warnings(warnings))
    }
}

struct AssembledExternalEquivalenceTask {
    pub stable_premises: Vec<problem::AnnotatedFormula>,
    pub forward_premises: Vec<problem::AnnotatedFormula>,
    pub forward_conclusions: Vec<problem::AnnotatedFormula>,
    pub backward_premises: Vec<problem::AnnotatedFormula>,
    pub backward_conclusions: Vec<problem::AnnotatedFormula>,
    pub proof_outline: ProofOutline,
    pub decomposition: Decomposition,
    pub direction: fol::Direction,
}

impl Task for AssembledExternalEquivalenceTask {
    type Error = ExternalEquivalenceTaskError;
    type Warning = ExternalEquivalenceTaskWarning;

    fn decompose(self) -> Result<Vec<Problem>, Self::Warning, Self::Error> {
        let mut problems = Vec::new();

        if matches!(
            self.direction,
            fol::Direction::Universal | fol::Direction::Forward
        ) {
            let mut axioms = self.stable_premises.clone();
            axioms.extend(self.forward_premises.clone());
            axioms.extend(
                self.proof_outline
                    .forward_definitions
                    .into_iter()
                    .map(|f| f.into_problem_formula(problem::Role::Axiom)),
            );

            for (i, lemma) in self.proof_outline.forward_lemmas.iter().enumerate() {
                for (j, conjecture) in lemma.conjectures.iter().enumerate() {
                    problems.push(
                        Problem::with_name(format!("forward_outline_{i}_{j}"))
                            .add_annotated_formulas(axioms.clone())
                            .add_annotated_formulas(std::iter::once(conjecture.clone()))
                            .rename_conflicting_symbols()
                            .create_unique_formula_names(),
                    );
                }
                axioms.append(&mut lemma.consequences.clone());
            }

            problems.append(
                &mut Problem::with_name("forward_problem")
                    .add_annotated_formulas(self.stable_premises.clone())
                    .add_annotated_formulas(self.forward_premises)
                    .add_annotated_formulas(
                        self.proof_outline
                            .forward_lemmas
                            .into_iter()
                            .flat_map(|g: GeneralLemma| g.consequences.into_iter()),
                    )
                    .add_annotated_formulas(self.forward_conclusions)
                    .rename_conflicting_symbols()
                    .create_unique_formula_names()
                    .decompose(self.decomposition),
            );
        }

        if matches!(
            self.direction,
            fol::Direction::Universal | fol::Direction::Backward
        ) {
            let mut axioms = self.stable_premises.clone();
            axioms.extend(self.backward_premises.clone());
            axioms.extend(
                self.proof_outline
                    .backward_definitions
                    .into_iter()
                    .map(|f| f.into_problem_formula(problem::Role::Axiom)),
            );

            for (i, lemma) in self.proof_outline.backward_lemmas.iter().enumerate() {
                for (j, conjecture) in lemma.conjectures.iter().enumerate() {
                    problems.push(
                        Problem::with_name(format!("backward_outline_{i}_{j}"))
                            .add_annotated_formulas(axioms.clone())
                            .add_annotated_formulas(std::iter::once(conjecture.clone()))
                            .rename_conflicting_symbols()
                            .create_unique_formula_names(),
                    );
                }
                axioms.append(&mut lemma.consequences.clone());
            }

            problems.append(
                &mut Problem::with_name("backward_problem")
                    .add_annotated_formulas(self.stable_premises)
                    .add_annotated_formulas(self.backward_premises)
                    .add_annotated_formulas(
                        self.proof_outline
                            .backward_lemmas
                            .into_iter()
                            .flat_map(|g: GeneralLemma| g.consequences.into_iter()),
                    )
                    .add_annotated_formulas(self.backward_conclusions)
                    .rename_conflicting_symbols()
                    .create_unique_formula_names()
                    .decompose(self.decomposition),
            );
        }

        Ok(WithWarnings::flawless(problems))
    }
}

#[cfg(test)]
mod tests {
    use {
        super::{DefinitionSequence, DefinitionSequenceNode, valid},
        crate::syntax_tree::fol,
        indexmap::IndexSet,
    };

    #[test]
    fn test_valid_case_1() {
        // input predicates: p
        // defined predicates: q
        let p = fol::Predicate {
            symbol: "p".to_string(),
            arity: 1,
        };
        let q = fol::Predicate {
            symbol: "q".to_string(),
            arity: 1,
        };

        // q(X) <-> p(X)
        let n1 = DefinitionSequenceNode {
            lhs: q.clone(),
            rhs: IndexSet::from_iter([p.clone()]),
        };

        let sequence = DefinitionSequence {
            nodes: vec![n1],
            base_predicates: IndexSet::from_iter([p.clone()]),
        };

        assert!(valid(&sequence, p));
        assert!(valid(&sequence, q));
    }

    #[test]
    fn test_valid_case_2() {
        // input predicates: p
        // defined predicates: q, r, t
        let p = fol::Predicate {
            symbol: "p".to_string(),
            arity: 1,
        };
        let q = fol::Predicate {
            symbol: "q".to_string(),
            arity: 1,
        };
        let r = fol::Predicate {
            symbol: "r".to_string(),
            arity: 1,
        };
        let t = fol::Predicate {
            symbol: "t".to_string(),
            arity: 1,
        };

        // q(X) <-> p(X)
        let n1 = DefinitionSequenceNode {
            lhs: q.clone(),
            rhs: IndexSet::from_iter([p.clone()]),
        };

        // r(X) <-> q(X)
        let n2 = DefinitionSequenceNode {
            lhs: r.clone(),
            rhs: IndexSet::from_iter([q.clone()]),
        };

        // t(X) <-> p(X) & q(X)
        let n3 = DefinitionSequenceNode {
            lhs: t.clone(),
            rhs: IndexSet::from_iter([p.clone(), q.clone()]),
        };

        let sequence = DefinitionSequence {
            nodes: vec![n1, n2, n3],
            base_predicates: IndexSet::from_iter([p.clone()]),
        };

        assert!(valid(&sequence, p));
        assert!(valid(&sequence, q));
        assert!(valid(&sequence, r));
        assert!(valid(&sequence, t));

        let x = fol::Predicate {
            symbol: "x".to_string(),
            arity: 1,
        };
        assert!(!valid(&sequence, x));
    }

    #[test]
    fn test_valid_case_3() {
        // input predicates: p
        // defined predicates: r, t
        // missing definitions: q
        let p = fol::Predicate {
            symbol: "p".to_string(),
            arity: 1,
        };
        let q = fol::Predicate {
            symbol: "q".to_string(),
            arity: 1,
        };
        let r = fol::Predicate {
            symbol: "r".to_string(),
            arity: 1,
        };
        let t = fol::Predicate {
            symbol: "r".to_string(),
            arity: 1,
        };

        // r(X) <-> q(X) & p(X)
        let n1 = DefinitionSequenceNode {
            lhs: r.clone(),
            rhs: IndexSet::from_iter([q.clone()]),
        };

        // t(X) <-> r(X)
        let n2 = DefinitionSequenceNode {
            lhs: r.clone(),
            rhs: IndexSet::from_iter([q.clone()]),
        };

        let sequence = DefinitionSequence {
            nodes: vec![n1, n2],
            base_predicates: IndexSet::from_iter([p.clone()]),
        };

        assert!(valid(&sequence, p));
        assert!(!valid(&sequence, q));
        assert!(!valid(&sequence, r));
        assert!(!valid(&sequence, t));
    }
}
