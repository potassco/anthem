use {
    crate::{
        command_line::arguments::{Decomposition, FormulaRepresentation},
        convenience::{
            apply::Apply as _,
            compose::Compose as _,
            with_warnings::{Result, WithWarnings},
        },
        simplifying::fol::sigma_0::{classic::CLASSIC, ht::HT, intuitionistic::INTUITIONISTIC},
        syntax_tree::{asp::mini_gringo as asp, fol::sigma_0 as fol},
        translating::{
            classical_reduction::gamma::{Gamma as _, Here as _, There as _},
            formula_representation::{mu::Mu as _, tau_star::TauStar as _},
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

            let hp = p.clone().to_formula().here();
            let tp = p.to_formula().there();

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

        let mut left = match self.formula_representation {
            FormulaRepresentation::Mu => self.left.mu(),
            FormulaRepresentation::TauStar => self.left.tau_star(),
        };

        let mut right = match self.formula_representation {
            FormulaRepresentation::Mu => self.right.mu(),
            FormulaRepresentation::TauStar => self.right.tau_star(),
        };

        if self.simplify {
            let mut portfolio = [INTUITIONISTIC, HT].concat().into_iter().compose();
            left = left
                .into_iter()
                .map(|f| f.apply_fixpoint(&mut portfolio))
                .collect();
            right = right
                .into_iter()
                .map(|f| f.apply_fixpoint(&mut portfolio))
                .collect();
        }

        left = left.gamma();
        right = right.gamma();

        if self.simplify {
            let mut portfolio = [INTUITIONISTIC, HT, CLASSIC].concat().into_iter().compose();
            left = left
                .into_iter()
                .map(|f| f.apply_fixpoint(&mut portfolio))
                .collect();
            right = right
                .into_iter()
                .map(|f| f.apply_fixpoint(&mut portfolio))
                .collect();
        }

        if self.break_equivalences {
            left = crate::breaking::fol::sigma_0::ht::break_equivalences_theory(left);
            right = crate::breaking::fol::sigma_0::ht::break_equivalences_theory(right);
        }

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
