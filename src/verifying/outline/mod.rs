use {
    crate::{
        convenience::{
            unbox::{Unbox as _, fol::sigma_0::UnboxedFormula},
            with_warnings::{Result, WithWarnings},
        },
        syntax_tree::fol::sigma_0 as fol,
        verifying::problem,
    },
    indexmap::{IndexMap, IndexSet},
    std::fmt::Display,
    thiserror::Error,
};

// If all the conjectures are proven,
// then all consequences can be added as axioms to the next proof step
// A basic lemma F has conjectures [F] and consequences [F]
// An inductive lemma F has conjectures [Base, Step] and axioms [F]
#[derive(Clone, Debug, PartialEq)]
pub struct GeneralLemma {
    pub conjectures: Vec<problem::AnnotatedFormula>,
    pub consequences: Vec<problem::AnnotatedFormula>,
}

impl TryFrom<fol::AnnotatedFormula> for GeneralLemma {
    type Error = ProofOutlineError;

    fn try_from(
        annotated_formula: fol::AnnotatedFormula,
    ) -> std::result::Result<Self, Self::Error> {
        match annotated_formula.role {
            fol::Role::Lemma => Ok(GeneralLemma {
                conjectures: vec![
                    annotated_formula
                        .clone()
                        .into_problem_formula(problem::Role::Conjecture),
                ],
                consequences: vec![annotated_formula.into_problem_formula(problem::Role::Axiom)],
            }),
            fol::Role::InductiveLemma => {
                let induction_formulas = annotated_formula.formula.clone().inductive_lemma()?;
                let (base, step) = induction_formulas.data;
                // TODO handle warnings
                let base_annotated = fol::AnnotatedFormula {
                    role: fol::Role::Lemma,
                    direction: annotated_formula.direction,
                    name: format!("{}base_case", annotated_formula.name),
                    formula: base,
                };
                let step_annotated = fol::AnnotatedFormula {
                    role: fol::Role::Lemma,
                    direction: annotated_formula.direction,
                    name: format!("{}inductive_step", annotated_formula.name),
                    formula: step,
                };
                Ok(GeneralLemma {
                    conjectures: vec![
                        base_annotated.into_problem_formula(problem::Role::Conjecture),
                        step_annotated.into_problem_formula(problem::Role::Conjecture),
                    ],
                    consequences: vec![
                        annotated_formula.into_problem_formula(problem::Role::Axiom),
                    ],
                })
            }
            fol::Role::Assumption | fol::Role::Spec | fol::Role::Definition => Err(
                ProofOutlineError::InvalidRoleForGeneralLemma(annotated_formula),
            ),
        }
    }
}

// TODO: Think about the name
trait CheckInternal {
    // Returns the predicate defined in the LHS of the formula if it is a valid definition, else returns an error
    fn definition(
        &self,
        taken_predicates: &IndexSet<fol::Predicate>,
    ) -> Result<fol::Predicate, ProofOutlineWarning, ProofOutlineError>;

    // Returns the base case and inductive step formulas if the formula is a valid inductive lemma, else returns an error
    fn inductive_lemma(
        self,
    ) -> Result<(fol::Formula, fol::Formula), ProofOutlineWarning, ProofOutlineError>;
}

impl CheckInternal for fol::Formula {
    fn definition(
        &self,
        taken_predicates: &IndexSet<fol::Predicate>,
    ) -> Result<fol::Predicate, ProofOutlineWarning, ProofOutlineError> {
        match self.clone().unbox() {
            UnboxedFormula::QuantifiedFormula {
                quantification:
                    fol::Quantification {
                        quantifier: fol::Quantifier::Forall,
                        variables,
                    },
                formula:
                    fol::Formula::BinaryFormula {
                        connective: fol::BinaryConnective::Equivalence,
                        lhs,
                        rhs,
                    },
            } => match lhs.unbox() {
                UnboxedFormula::AtomicFormula(fol::AtomicFormula::Atom(a)) => {
                    let mut warnings = Vec::new();

                    // check variables has no duplicates
                    let len = variables.len();
                    let uniques: IndexSet<fol::Variable> = IndexSet::from_iter(variables);
                    if uniques.len() < len {
                        return Err(ProofOutlineError::DuplicatedVariables(self.clone()));
                    }

                    let mut terms_as_vars = IndexSet::new();
                    for t in a.terms.iter() {
                        match fol::Variable::try_from(t.clone()) {
                            Ok(v) => {
                                terms_as_vars.insert(v);
                            }
                            Err(e) => {
                                return Err(ProofOutlineError::TermsInDefinition {
                                    term: e,
                                    formula: self.clone(),
                                });
                            }
                        }
                    }

                    // Check variables in quantifications are the same as the terms in the atom
                    if uniques != terms_as_vars {
                        return Err(ProofOutlineError::DefinedPredicateVariableListMismatch(
                            self.clone(),
                        ));
                    }

                    // check predicate is totally fresh
                    let predicate = a.predicate();
                    if taken_predicates.contains(&predicate) {
                        return Err(ProofOutlineError::TakenPredicate(predicate));
                    }

                    // check RHS has no free variables other than those in uniques
                    if rhs.free_variables().difference(&uniques).next().is_some() {
                        return Err(ProofOutlineError::FreeRhsVariables(self.clone()));
                    }

                    // warn the user if the RHS is missing some variable from the quantification
                    if uniques.difference(&rhs.free_variables()).next().is_some() {
                        warnings.push(ProofOutlineWarning::ExcessQuantifiedVariables(self.clone()));
                    }

                    // check RHS has no predicates other than taken predicates
                    // this should ensure no recursion through definition sequence
                    if let Some(predicate) = rhs.predicates().difference(taken_predicates).next() {
                        return Err(ProofOutlineError::UndefinedRhsPredicate {
                            definition: self.clone(),
                            predicate: predicate.clone(),
                        });
                    }

                    Ok(WithWarnings::flawless(predicate).preface_warnings(warnings))
                }
                _ => Err(ProofOutlineError::MalformedDefinition(self.clone())),
            },

            _ => Err(ProofOutlineError::MalformedDefinition(self.clone())),
        }
    }

    fn inductive_lemma(
        self,
    ) -> Result<(fol::Formula, fol::Formula), ProofOutlineWarning, ProofOutlineError> {
        let original = self.clone();
        match self.unbox() {
            UnboxedFormula::QuantifiedFormula {
                quantification:
                    fol::Quantification {
                        quantifier: fol::Quantifier::Forall,
                        variables,
                    },
                formula:
                    fol::Formula::BinaryFormula {
                        connective: fol::BinaryConnective::Implication,
                        lhs,
                        rhs,
                    },
            } => match lhs.clone().unbox() {
                UnboxedFormula::AtomicFormula(fol::AtomicFormula::Comparison(
                    fol::Comparison { term, guards },
                )) => {
                    if guards.len() != 1 {
                        return Err(ProofOutlineError::MalformedInductiveAntecedent(original));
                    }
                    let varset: IndexSet<fol::Variable> = IndexSet::from_iter(variables.clone());
                    if varset != rhs.free_variables() {
                        return Err(ProofOutlineError::MalformedInductiveVariables(original));
                    }

                    let induction_variable = match term {
                        fol::GeneralTerm::IntegerTerm(fol::IntegerTerm::Variable(ref v)) => {
                            fol::Variable {
                                name: v.to_string(),
                                sort: fol::Sort::Integer,
                            }
                        }
                        _ => return Err(ProofOutlineError::MalformedInductiveTerm(original)),
                    };

                    let guard = guards[0].clone();

                    match term {
                        fol::GeneralTerm::IntegerTerm(induction_term) => match guard {
                            fol::Guard {
                                relation: fol::Relation::GreaterEqual,
                                term: fol::GeneralTerm::IntegerTerm(fol::IntegerTerm::Numeral(n)),
                            } => {
                                let least_term =
                                    fol::GeneralTerm::IntegerTerm(fol::IntegerTerm::Numeral(n));
                                let base_case = rhs
                                    .clone()
                                    .substitute(induction_variable.clone(), least_term)
                                    .universal_closure();
                                let inductive_step_antecedent = fol::Formula::BinaryFormula {
                                    connective: fol::BinaryConnective::Conjunction,
                                    lhs: lhs.clone(),
                                    rhs: rhs.clone(),
                                };

                                let successor = fol::GeneralTerm::IntegerTerm(
                                    fol::IntegerTerm::BinaryOperation {
                                        op: fol::BinaryOperator::Add,
                                        lhs: induction_term.clone().into(),
                                        rhs: fol::IntegerTerm::Numeral(1).into(),
                                    },
                                );

                                let inductive_step_consequent =
                                    rhs.substitute(induction_variable.clone(), successor);
                                let inductive_step = fol::Formula::BinaryFormula {
                                    connective: fol::BinaryConnective::Implication,
                                    lhs: inductive_step_antecedent.into(),
                                    rhs: inductive_step_consequent.into(),
                                }
                                .universal_closure();

                                Ok(WithWarnings::flawless((base_case, inductive_step)))
                            }
                            _ => Err(ProofOutlineError::MalformedInductiveLemma(original)),
                        },
                        _ => Err(ProofOutlineError::MalformedInductiveLemma(original)),
                    }
                }
                _ => Err(ProofOutlineError::MalformedInductiveLemma(original)),
            },
            _ => Err(ProofOutlineError::MalformedInductiveLemma(original)),
        }
    }
}

#[derive(Error, Debug, PartialEq)]
pub enum ProofOutlineError {
    #[error("the following annotated formula has a role that is forbidden in proof outlines: {0}")]
    AnnotatedFormulaWithInvalidRole(fol::AnnotatedFormula),
    #[error(
        "the following definiton contains duplicated variables in outermost quantification: {0}"
    )]
    DuplicatedVariables(fol::Formula),
    #[error("definitions require fresh predicates but the following predicate is taken: {0}")]
    TakenPredicate(fol::Predicate),
    #[error("the following definition contains free variables in the RHS: {0}")]
    FreeRhsVariables(fol::Formula),
    #[error(
        "undefined predicate -- `{predicate}` occurs for the first time in the RHS of definition `{definition}`"
    )]
    UndefinedRhsPredicate {
        definition: fol::Formula,
        predicate: fol::Predicate,
    },
    #[error(
        "the following definition has different variables in the LHS than the universal quantification: `{0}`"
    )]
    DefinedPredicateVariableListMismatch(fol::Formula),
    #[error(
        "the LHS of the following definition contains the non-variable term `{term}` : `{formula}`"
    )]
    TermsInDefinition {
        term: fol::GeneralTerm,
        formula: fol::Formula,
    },
    #[error("the following inductive lemma is malformed: `{0}`")]
    MalformedInductiveLemma(fol::Formula),
    #[error("the antecedent of the following inductive lemma is malformed: `{0}`")]
    MalformedInductiveAntecedent(fol::Formula),
    #[error(
        "the universally quantified variables in the following inductive lemma do not match the RHS free variables: `{0}`"
    )]
    MalformedInductiveVariables(fol::Formula),
    #[error(
        "the inductive term in the following inductive lemma is not an integer variable: `{0}`"
    )]
    MalformedInductiveTerm(fol::Formula),
    #[error("the following definition is malformed: {0}")]
    MalformedDefinition(fol::Formula),
    #[error("the following annotated formula cannot be converted to a general lemma: `{0}`")]
    InvalidRoleForGeneralLemma(fol::AnnotatedFormula),
}

pub struct ProofOutline {
    pub forward_lemmas: Vec<GeneralLemma>,
    pub backward_lemmas: Vec<GeneralLemma>,
    pub forward_definitions: Vec<fol::AnnotatedFormula>,
    pub backward_definitions: Vec<fol::AnnotatedFormula>,
}

#[derive(Error, Debug, Eq, PartialEq)]
pub enum ProofOutlineWarning {
    ExcessQuantifiedVariables(fol::Formula),
}

impl Display for ProofOutlineWarning {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ProofOutlineWarning::ExcessQuantifiedVariables(formula) => {
                writeln!(
                    f,
                    "the universally quantified list of variables contains members which do not occur in the RHS of {formula}"
                )
            }
        }
    }
}

impl ProofOutline {
    pub fn from_specification(
        specification: fol::Specification,
        mut taken_predicates: IndexSet<fol::Predicate>,
        placeholders: &IndexMap<String, fol::FunctionConstant>,
    ) -> Result<Self, ProofOutlineWarning, ProofOutlineError> {
        let mut warnings = Vec::new();

        let mut forward_lemmas = Vec::new();
        let mut backward_lemmas = Vec::new();
        let mut forward_definitions = Vec::new();
        let mut backward_definitions = Vec::new();

        for anf in specification.formulas {
            let anf = anf.replace_placeholders(placeholders);
            match anf.role {
                fol::Role::Lemma | fol::Role::InductiveLemma => {
                    let general_lemma: GeneralLemma = anf
                        .universal_closure_with_quantifier_joining()
                        .replace_placeholders(placeholders)
                        .try_into()?;
                    match anf.direction {
                        fol::Direction::Universal => {
                            forward_lemmas.push(general_lemma.clone());
                            backward_lemmas.push(general_lemma);
                        }
                        fol::Direction::Forward => forward_lemmas.push(general_lemma),
                        fol::Direction::Backward => backward_lemmas.push(general_lemma),
                    }
                }
                fol::Role::Definition => {
                    let predicate = anf.formula.definition(&taken_predicates)?;
                    taken_predicates.insert(predicate.data);
                    warnings.extend(predicate.warnings);
                    match anf.direction {
                        fol::Direction::Forward => {
                            forward_definitions.push(anf);
                        }
                        fol::Direction::Backward => {
                            backward_definitions.push(anf);
                        }
                        fol::Direction::Universal => {
                            forward_definitions.push(anf.clone());
                            backward_definitions.push(anf);
                        }
                    }
                }
                fol::Role::Assumption | fol::Role::Spec => {
                    return Err(ProofOutlineError::AnnotatedFormulaWithInvalidRole(anf));
                }
            }
        }

        Ok(WithWarnings::flawless(ProofOutline {
            forward_lemmas,
            backward_lemmas,
            forward_definitions,
            backward_definitions,
        })
        .preface_warnings(warnings))
    }
}

#[cfg(test)]
mod tests {
    use {
        super::{CheckInternal, ProofOutlineError},
        crate::syntax_tree::fol::sigma_0 as fol,
        indexmap::IndexSet,
    };

    #[test]
    fn check_correct_definition() {
        for (src, target) in [
            (
                "forall X ( p(X) <-> 1 < 2 )",
                fol::Predicate {
                    symbol: "p".to_string(),
                    arity: 1,
                },
            ),
            (
                "forall X Y$i ( pred(X, Y$i) <-> exists N$i (X = N$i and t(X) or t(Y$i)) )",
                fol::Predicate {
                    symbol: "pred".to_string(),
                    arity: 2,
                },
            ),
        ] {
            let taken_predicates: IndexSet<fol::Predicate> =
                IndexSet::from_iter(vec![fol::Predicate {
                    symbol: "t".to_string(),
                    arity: 1,
                }]);
            let formula: fol::Formula = src.parse().unwrap();
            assert_eq!(formula.definition(&taken_predicates).unwrap().data, target)
        }
    }

    #[test]
    fn check_incorrect_definition() {
        for (src, target) in [
            (
                "forall X Y X ( p(X) <-> 1 < 2 )",
                ProofOutlineError::DuplicatedVariables(
                    "forall X Y X ( p(X) <-> 1 < 2 )".parse().unwrap(),
                ),
            ),
            (
                "forall X ( t(X) <-> 1 < 2 )",
                ProofOutlineError::TakenPredicate(fol::Predicate {
                    symbol: "t".to_string(),
                    arity: 1,
                }),
            ),
            (
                "forall Z1 Z2 ( ancestor(Z1, Z2) <-> t(X) and t(Z2) )",
                ProofOutlineError::FreeRhsVariables(
                    "forall Z1 Z2 ( ancestor(Z1, Z2) <-> t(X) and t(Z2) )"
                        .parse()
                        .unwrap(),
                ),
            ),
            (
                "forall Z1 Z2 ( ancestor(Z1, Z2) <-> ancestor(Z1, Z2) )",
                ProofOutlineError::UndefinedRhsPredicate {
                    definition: "forall Z1 Z2 ( ancestor(Z1, Z2) <-> ancestor(Z1, Z2) )"
                        .parse()
                        .unwrap(),
                    predicate: fol::Predicate {
                        symbol: "ancestor".to_string(),
                        arity: 2,
                    },
                },
            ),
        ] {
            let taken_predicates: IndexSet<fol::Predicate> =
                IndexSet::from_iter(vec![fol::Predicate {
                    symbol: "t".to_string(),
                    arity: 1,
                }]);
            let formula: fol::Formula = src.parse().unwrap();
            assert_eq!(formula.definition(&taken_predicates), Err(target))
        }
    }

    #[test]
    fn test_correct_inductive_lemma() {
        for (src, base, step) in [
            (
                "forall I$i ( I$i >= 5 -> p(I$i) )",
                "p(5)",
                "forall I$i ( (I$i >= 5 and p(I$i)) -> p(I$i+1) )",
            ),
            (
                "forall N$i ( N$i >= 1 -> squareLEb(N$i) )",
                "squareLEb(1)",
                "forall N$i ( (N$i >= 1 and squareLEb(N$i)) -> squareLEb(N$i+1) )",
            ),
            (
                "forall I$ ( I$ >= 5 -> (p(I$) and not q(I$,5)) )",
                "p(5) and not q(5,5)",
                "forall I$ ( ( I$ >= 5 and (p(I$) and not q(I$,5)) ) -> ( p(I$+1) and not q(I$+1,5) ) )",
            ),
            (
                "forall N$i X ( N$i >= 0 -> (p(N$i,X) -> X = N$i) )",
                "forall X ( p(0,X) -> X = 0 )",
                "forall N$i X ( N$i >= 0 and (p(N$i,X) -> X = N$i) -> (p(N$i+1,X) -> X = N$i+1) )",
            ),
            (
                "forall M$i N$i ( N$i >= 0 -> N$i + M$i >= M$i )",
                "forall M$i ( 0 + M$i >= M$i )",
                "forall M$i N$i ( N$i >= 0 and N$i + M$i >= M$i -> (N$i+1 + M$i >= M$i) )",
            ),
        ] {
            let formula: fol::Formula = src.parse().unwrap();
            let (base_result, step_result) = formula.inductive_lemma().unwrap().data;
            let (base_target, step_target): (fol::Formula, fol::Formula) =
                (base.parse().unwrap(), step.parse().unwrap());
            assert_eq!(
                (base_result.clone(), step_result.clone()),
                (base_target.clone(), step_target.clone()),
                "\n({base_result},{step_result})\n != \n({base_target},{step_target})"
            )
        }
    }

    #[test]
    fn check_incorrect_inductive_lemma() {
        for (src, target) in [
            (
                "forall X ( X >= 0 -> p(X) )",
                ProofOutlineError::MalformedInductiveTerm(
                    "forall X ( X >= 0 -> p(X) )".parse().unwrap(),
                ),
            ),
            (
                "forall X$i ( X$i > 0 -> p(X$i) )",
                ProofOutlineError::MalformedInductiveLemma(
                    "forall X$i ( X$i > 0 -> p(X$i) )".parse().unwrap(),
                ),
            ),
            (
                "forall X$i ( X$i >= 0 -> p(X$i, Y$i) )",
                ProofOutlineError::MalformedInductiveVariables(
                    "forall X$i ( X$i >= 0 -> p(X$i, Y$i) )".parse().unwrap(),
                ),
            ),
        ] {
            let formula: fol::Formula = src.parse().unwrap();
            assert_eq!(formula.inductive_lemma(), Err(target))
        }
    }
}
