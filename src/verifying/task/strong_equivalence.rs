use {
    crate::{
        command_line::arguments::{Decomposition, FormulaRepresentation},
        convenience::{
            apply::Apply as _,
            compose::Compose as _,
            with_warnings::{Result, WithWarnings},
        },
        simplifying::fol::{classic::CLASSIC, ht::HT, intuitionistic::INTUITIONISTIC},
        syntax_tree::{asp, fol::{self, Theory}},
        translating::{
            gamma::{self, gamma_formula},
            mu::mu,
            tau_star::tau_star_with_axioms,
        },
        verifying::{
            outline::{GeneralLemma, ProofOutline, ProofOutlineError, ProofOutlineWarning},
            problem::{self, AnnotatedFormula, Problem, Role},
            task::Task,
        },
    },
    indexmap::{IndexMap, IndexSet},
    std::fmt::Display,
    thiserror::Error,
};

#[derive(Error, Debug)]
pub enum StrongEquivalenceTaskWarning {
    DefinitionWithWarning(#[from] ProofOutlineWarning),
}

impl Display for StrongEquivalenceTaskWarning {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            StrongEquivalenceTaskWarning::DefinitionWithWarning(w) => writeln!(f, "{w}"),
        }
    }
}

#[derive(Error, Debug)]
pub enum StrongEquivalenceTaskError {
    ProofOutlineError(#[from] ProofOutlineError),
}

impl Display for StrongEquivalenceTaskError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            StrongEquivalenceTaskError::ProofOutlineError(_) => {
                writeln!(f, "the given proof outline contains errors")
            }
        }
    }
}

fn transition(p: fol::Predicate) -> fol::Formula {
    let hp = gamma::here(p.clone().to_formula());
    let tp = gamma::there(p.to_formula());

    let variables = hp.free_variables();

    fol::Formula::BinaryFormula {
        connective: fol::BinaryConnective::Implication,
        lhs: hp.into(),
        rhs: tp.into(),
    }
    .quantify(fol::Quantifier::Forall, variables.into_iter().collect())
}

fn add_transition_axioms(mut axioms: Vec<fol::Formula>, formulas: &Vec<fol::Formula>) -> Vec<fol::Formula> {
    let mut transition_axioms: IndexSet<fol::Formula> = IndexSet::from_iter(axioms.drain(..));
    for formula in formulas {
        for predicate in formula.predicates() {
            transition_axioms.insert(transition(predicate));
        }
    }
    Vec::from_iter(transition_axioms)
}

pub struct StrongEquivalenceTask {
    pub left: asp::Program,
    pub right: asp::Program,
    pub proof_outline: fol::Specification,
    pub decomposition: Decomposition,
    pub direction: fol::Direction,
    pub formula_representation: FormulaRepresentation,
    pub simplify: bool,
    pub break_equivalences: bool,
}

impl StrongEquivalenceTask {
    fn transition_axioms(&self) -> fol::Theory {
        fn proof_outline_predicates_transition(f: &fol::AnnotatedFormula) -> Vec<fol::Formula> {
            f.predicates().into_iter().map(transition).collect()
        }

        let mut program_predicates = self.left.predicates();
        program_predicates.extend(self.right.predicates());

        let mut formulas: IndexSet<fol::Formula> =
            IndexSet::from_iter(program_predicates.into_iter().map(|p| transition(p.into())));

        formulas.extend(
            self.proof_outline
                .formulas
                .iter()
                .flat_map(proof_outline_predicates_transition),
        );

        fol::Theory {
            formulas: Vec::from_iter(formulas),
        }
    }
}

impl Task for StrongEquivalenceTask {
    type Error = StrongEquivalenceTaskError;
    type Warning = StrongEquivalenceTaskWarning;

    fn decompose(self) -> Result<Vec<Problem>, Self::Warning, Self::Error> {
        let placeholders = IndexMap::new(); // Strong equivalence doesn't support placeholders yet

        // These are the "forall X (hp(X) -> tp(X))" axioms.
        let base_transition_axioms = self.transition_axioms().formulas;

        // Map aggregate elements to names for creating new predicate constants
        let mut combined_program = self.left.clone();
        combined_program.rules.extend(self.right.rules.clone());
        let aggregate_names = combined_program.aggregate_names();

        // Apply formula representation transformation and generate supporting counting axioms
        let (mut left_formulas, left_axioms) = match self.formula_representation {
            FormulaRepresentation::Mu => {
                let formulas = mu(self.left).formulas;
                (formulas, vec![])
            }
            FormulaRepresentation::TauStar => {
                let theory = tau_star_with_axioms(self.left, Some(aggregate_names.clone()));
                (theory.formulas, theory.axioms)
            }
        };

        let (mut right_formulas, right_axioms) = match self.formula_representation {
            FormulaRepresentation::Mu => {
                let formulas = mu(self.right).formulas;
                (formulas, vec![])
            }
            FormulaRepresentation::TauStar => {
                let theory = tau_star_with_axioms(self.right, Some(aggregate_names.clone()));
                (theory.formulas, theory.axioms)
            }
        };

        // Taken predicates are off-limits to definitions within proof outlines
        let mut taken_predicates = IndexSet::new();
        for formula in left_formulas.iter() {
            taken_predicates.extend(formula.predicates());
        }
        for formula in right_formulas.iter() {
            taken_predicates.extend(formula.predicates());
        }

        // Apply HT-equivalent simplifications
        if self.simplify {
            let mut portfolio = [INTUITIONISTIC, HT].concat().into_iter().compose();
            left_formulas = left_formulas
                .into_iter()
                .map(|f| f.apply_fixpoint(&mut portfolio))
                .collect();
            right_formulas = right_formulas
                .into_iter()
                .map(|f| f.apply_fixpoint(&mut portfolio))
                .collect();
        }

        // Apply gamma to formula representations of programs
        left_formulas = left_formulas.into_iter().map(gamma_formula).collect(); 
        right_formulas = right_formulas.into_iter().map(gamma_formula).collect(); 

        // Apply classical simplifications
        if self.simplify {
            let mut portfolio = [INTUITIONISTIC, HT, CLASSIC].concat().into_iter().compose();
            left_formulas = left_formulas
                .into_iter()
                .map(|f| f.apply_fixpoint(&mut portfolio))
                .collect();
            right_formulas = right_formulas
                .into_iter()
                .map(|f| f.apply_fixpoint(&mut portfolio))
                .collect();
        }

        let left_theory = Theory {formulas: left_formulas};
        let right_theory = Theory {formulas: right_formulas};

        if self.break_equivalences {
            // equivalence breaking should only be applied to conjectures, not axioms
            println!("equivalence breaking is currently ignored");
            // left_theory = crate::breaking::fol::ht::break_equivalences_theory(left_theory);
            // right_theory = crate::breaking::fol::ht::break_equivalences_theory(right_theory);
        }

        // Apply gamma to supporting counting axioms
        let mut counting_axioms_formulas: Vec<fol::Formula> = left_axioms.into_iter().map(gamma_formula).collect();
        counting_axioms_formulas.extend(right_axioms.into_iter().map(gamma_formula));

        // Extend transition axioms and taken_predicates with newly generated predicate symbols    
        let transition_axioms = Theory { formulas: add_transition_axioms(base_transition_axioms, &counting_axioms_formulas) };
        for formula in counting_axioms_formulas.iter() {
            taken_predicates.extend(formula.predicates());
        }

        let mut warnings = Vec::new();

        let proof_outline_construction =
            ProofOutline::from_specification(self.proof_outline, taken_predicates, &placeholders)?;
        warnings.extend(
            proof_outline_construction
                .warnings
                .into_iter()
                .map(StrongEquivalenceTaskWarning::from),
        );

        Ok(AssembledStrongEquivalenceTask {
            transition_axioms,
            left: left_theory,
            right: right_theory,
            counting_axioms: Theory { formulas: counting_axioms_formulas },
            proof_outline: proof_outline_construction.data,
            decomposition: self.decomposition,
            direction: self.direction,
        }
        .decompose()?
        .preface_warnings(warnings))
    }
}

struct AssembledStrongEquivalenceTask {
    pub transition_axioms: fol::Theory,
    pub counting_axioms: fol::Theory,
    pub left: fol::Theory,
    pub right: fol::Theory,
    pub proof_outline: ProofOutline,
    pub decomposition: Decomposition,
    pub direction: fol::Direction,
}

impl Task for AssembledStrongEquivalenceTask {
    type Error = StrongEquivalenceTaskError;
    type Warning = StrongEquivalenceTaskWarning;

    fn decompose(self) -> Result<Vec<Problem>, Self::Warning, Self::Error> {
        let proof_outline = self.proof_outline.apply_gamma_reduction();

        let mut problems = Vec::new();

        if matches!(
            self.direction,
            fol::Direction::Universal | fol::Direction::Forward
        ) {
            let mut forward_axioms: Vec<problem::AnnotatedFormula> = proof_outline
                .forward_definitions
                .into_iter()
                .map(|f| f.into_problem_formula(problem::Role::Axiom))
                .collect();

            for (i, lemma) in proof_outline.forward_lemmas.iter().enumerate() {
                for (j, conjecture) in lemma.conjectures.iter().enumerate() {
                    problems.push(
                        Problem::with_name(format!("forward_outline_{i}_{j}"))
                            .add_theory(self.transition_axioms.clone(), |i, formula| {
                                AnnotatedFormula {
                                    name: format!("transition_axiom_{i}"),
                                    role: Role::Axiom,
                                    formula,
                                }
                            })
                            .add_theory(self.counting_axioms.clone(), |i, formula| AnnotatedFormula {
                                name: format!("counting_axiom_{i}"),
                                role: Role::Axiom,
                                formula,
                            })
                            .add_annotated_formulas(forward_axioms.clone())
                            .add_theory(self.left.clone(), |i, formula| AnnotatedFormula {
                                name: format!("left_{i}"),
                                role: Role::Axiom,
                                formula,
                            })
                            .add_annotated_formulas(std::iter::once(conjecture.clone()))
                            .rename_conflicting_symbols()
                            .create_unique_formula_names(),
                    );
                }
                forward_axioms.append(&mut lemma.consequences.clone());
            }

            problems.append(
                &mut Problem::with_name("forward")
                    .add_theory(self.transition_axioms.clone(), |i, formula| {
                        AnnotatedFormula {
                            name: format!("transition_axiom_{i}"),
                            role: Role::Axiom,
                            formula,
                        }
                    })
                    .add_theory(self.counting_axioms.clone(), |i, formula| AnnotatedFormula {
                        name: format!("counting_axiom_{i}"),
                        role: Role::Axiom,
                        formula,
                    })
                    .add_annotated_formulas(
                        proof_outline
                            .forward_lemmas
                            .into_iter()
                            .flat_map(|g: GeneralLemma| g.consequences.into_iter()),
                    )
                    .add_theory(self.left.clone(), |i, formula| AnnotatedFormula {
                        name: format!("left_{i}"),
                        role: Role::Axiom,
                        formula,
                    })
                    .add_theory(self.right.clone(), |i, formula| AnnotatedFormula {
                        name: format!("right_{i}"),
                        role: Role::Conjecture,
                        formula,
                    })
                    .rename_conflicting_symbols()
                    .create_unique_formula_names()
                    .decompose(self.decomposition),
            );
        }
        if matches!(
            self.direction,
            fol::Direction::Universal | fol::Direction::Backward
        ) {
            let mut backward_axioms: Vec<problem::AnnotatedFormula> = proof_outline
                .backward_definitions
                .into_iter()
                .map(|f| f.into_problem_formula(problem::Role::Axiom))
                .collect();

            for (i, lemma) in proof_outline.backward_lemmas.iter().enumerate() {
                for (j, conjecture) in lemma.conjectures.iter().enumerate() {
                    problems.push(
                        Problem::with_name(format!("backward_outline_{i}_{j}"))
                            .add_theory(self.transition_axioms.clone(), |i, formula| {
                                AnnotatedFormula {
                                    name: format!("transition_axiom_{i}"),
                                    role: Role::Axiom,
                                    formula,
                                }
                            })
                            .add_theory(self.counting_axioms.clone(), |i, formula| AnnotatedFormula {
                                name: format!("counting_axiom_{i}"),
                                role: Role::Axiom,
                                formula,
                            })
                            .add_annotated_formulas(backward_axioms.clone())
                            .add_theory(self.right.clone(), |i, formula| AnnotatedFormula {
                                name: format!("right_{i}"),
                                role: Role::Axiom,
                                formula,
                            })
                            .add_annotated_formulas(std::iter::once(conjecture.clone()))
                            .rename_conflicting_symbols()
                            .create_unique_formula_names(),
                    );
                }
                backward_axioms.append(&mut lemma.consequences.clone());
            }

            problems.append(
                &mut Problem::with_name("backward")
                    .add_theory(self.transition_axioms.clone(), |i, formula| {
                        AnnotatedFormula {
                            name: format!("transition_axiom_{i}"),
                            role: Role::Axiom,
                            formula,
                        }
                    })
                    .add_theory(self.counting_axioms.clone(), |i, formula| AnnotatedFormula {
                        name: format!("counting_axiom_{i}"),
                        role: Role::Axiom,
                        formula,
                    })
                    .add_annotated_formulas(
                        proof_outline
                            .backward_lemmas
                            .into_iter()
                            .flat_map(|g: GeneralLemma| g.consequences.into_iter()),
                    )
                    .add_theory(self.right.clone(), |i, formula| AnnotatedFormula {
                        name: format!("right_{i}"),
                        role: Role::Axiom,
                        formula,
                    })
                    .add_theory(self.left.clone(), |i, formula| AnnotatedFormula {
                        name: format!("left_{i}"),
                        role: Role::Conjecture,
                        formula,
                    })
                    .rename_conflicting_symbols()
                    .create_unique_formula_names()
                    .decompose(self.decomposition),
            );
        }

        Ok(WithWarnings::flawless(problems))
    }
}
