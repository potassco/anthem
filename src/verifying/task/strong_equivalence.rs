use {
    crate::{
        command_line::arguments::{Decomposition, FormulaRepresentation},
        convenience::{
            apply::Apply as _,
            compose::Compose as _,
            with_warnings::{Result, WithWarnings},
        },
        simplifying::fol::{
            classic::CLASSIC,
            ht::{HT, exactly_axioms},
            intuitionistic::INTUITIONISTIC,
        },
        syntax_tree::{asp, fol},
        translating::{
            gamma::{self, gamma},
            mu::mu,
            tau_star::tau_star_with_axioms,
        },
        verifying::{
            problem::{AnnotatedFormula, Problem, Role},
            task::Task,
        },
    },
    std::convert::Infallible,
    thiserror::Error,
};

#[derive(Error, Debug)]
pub enum StrongEquivalenceTaskError {}

pub struct StrongEquivalenceTask {
    pub left: asp::Program,
    pub right: asp::Program,
    pub decomposition: Decomposition,
    pub direction: fol::Direction,
    pub formula_representation: FormulaRepresentation,
    pub simplify: bool,
    pub break_equivalences: bool,
}

impl StrongEquivalenceTask {
    fn transition_axioms(&self) -> fol::Theory {
        fn transition(p: asp::Predicate) -> fol::Formula {
            let p: fol::Predicate = p.into();

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

        let mut predicates = self.left.predicates();
        predicates.extend(self.right.predicates());

        fol::Theory {
            formulas: predicates.into_iter().map(transition).collect(),
        }
    }
}

impl Task for StrongEquivalenceTask {
    type Error = StrongEquivalenceTaskError;
    type Warning = Infallible;

    fn decompose(self) -> Result<Vec<Problem>, Self::Warning, Self::Error> {
        let transition_axioms = self.transition_axioms(); // These are the "forall X (hp(X) -> tp(X))" axioms.

        let mut combined_program = self.left.clone();
        combined_program.rules.extend(self.right.rules.clone());
        let aggregate_names = combined_program.aggregate_names();

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
                let theory = tau_star_with_axioms(self.right, Some(aggregate_names));
                (theory.formulas, theory.axioms)
            }
        };

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

        left_formulas = gamma(fol::Theory::from_iter(left_formulas)).formulas;
        right_formulas = gamma(fol::Theory::from_iter(right_formulas)).formulas;

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

        let (left, right) = if self.break_equivalences {
            (
                crate::breaking::fol::ht::break_equivalences_theory(fol::Theory::from_iter(
                    left_formulas,
                )),
                crate::breaking::fol::ht::break_equivalences_theory(fol::Theory::from_iter(
                    right_formulas,
                )),
            )
        } else {
            (
                fol::Theory::from_iter(left_formulas),
                fol::Theory::from_iter(right_formulas),
            )
        };

        let mut combined_theory = left.formulas.clone();
        combined_theory.extend(right.formulas.clone());
        let exactly_axioms = exactly_axioms(fol::Theory::from_iter(combined_theory));

        let mut counting_axioms_formulas = gamma(fol::Theory::from_iter(left_axioms)).formulas;
        counting_axioms_formulas.extend(gamma(fol::Theory::from_iter(right_axioms)).formulas);
        counting_axioms_formulas.extend(gamma(exactly_axioms).formulas);

        let counting_axioms = fol::Theory::from_iter(counting_axioms_formulas);

        let mut problems = Vec::new();
        if matches!(
            self.direction,
            fol::Direction::Universal | fol::Direction::Forward
        ) {
            problems.push(
                Problem::with_name("forward")
                    .add_theory(transition_axioms.clone(), |i, formula| AnnotatedFormula {
                        name: format!("transition_axiom_{i}"),
                        role: Role::Axiom,
                        formula,
                    })
                    .add_theory(counting_axioms.clone(), |i, formula| AnnotatedFormula {
                        name: format!("counting_axiom_{i}"),
                        role: Role::Axiom,
                        formula,
                    })
                    .add_theory(left.clone(), |i, formula| AnnotatedFormula {
                        name: format!("left_{i}"),
                        role: Role::Axiom,
                        formula,
                    })
                    .add_theory(right.clone(), |i, formula| AnnotatedFormula {
                        name: format!("right_{i}"),
                        role: Role::Conjecture,
                        formula,
                    })
                    .rename_conflicting_symbols()
                    .create_unique_formula_names(),
            );
        }
        if matches!(
            self.direction,
            fol::Direction::Universal | fol::Direction::Backward
        ) {
            problems.push(
                Problem::with_name("backward")
                    .add_theory(transition_axioms, |i, formula| AnnotatedFormula {
                        name: format!("transition_axiom_{i}"),
                        role: Role::Axiom,
                        formula,
                    })
                    .add_theory(counting_axioms, |i, formula| AnnotatedFormula {
                        name: format!("counting_axiom_{i}"),
                        role: Role::Axiom,
                        formula,
                    })
                    .add_theory(right, |i, formula| AnnotatedFormula {
                        name: format!("right_{i}"),
                        role: Role::Axiom,
                        formula,
                    })
                    .add_theory(left, |i, formula| AnnotatedFormula {
                        name: format!("left_{i}"),
                        role: Role::Conjecture,
                        formula,
                    })
                    .rename_conflicting_symbols()
                    .create_unique_formula_names(),
            );
        }

        Ok(WithWarnings::flawless(
            problems
                .into_iter()
                .flat_map(|p: Problem| match self.decomposition {
                    Decomposition::Independent => p.decompose_independent(),
                    Decomposition::Sequential => p.decompose_sequential(),
                })
                .collect(),
        ))
    }
}
