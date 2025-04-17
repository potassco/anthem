use crate::{
    convenience::apply::Apply as _,
    syntax_tree::fol::{Formula, Theory},
    verifying::problem::{AnnotatedFormula, Problem, Role},
};

pub mod classic;
pub mod ht;
pub mod intuitionistic;

impl From<Formula> for Theory {
    fn from(formula: Formula) -> Self {
        Theory {
            formulas: vec![formula],
        }
    }
}

pub fn validate_simplifications(formula: Formula) -> Vec<crate::verifying::problem::Problem> {
    use classic;

    let mut formulas = vec![(formula.clone(), "original".to_string())];

    let mut f1 = formula;
    let mut f2;

    loop {
        f2 = f1.clone().apply(&mut classic::remove_double_negation);
        formulas.push((f2.clone(), "remove_double_negation".to_string()));

        f2 = f2.apply(&mut classic::substitute_defined_variables)
            .apply(&mut intuitionistic::remove_orphaned_variables)
            .apply(&mut intuitionistic::remove_empty_quantifications);
        formulas.push((f2.clone(), "substitute_defined_variables".to_string()));

        f2 = f2.apply(&mut classic::unstable::restrict_quantifier_domain)
            .apply(&mut intuitionistic::remove_orphaned_variables)
            .apply(&mut intuitionistic::remove_empty_quantifications);
        formulas.push((f2.clone(), "restrict_quantifier_domain".to_string()));

        f2 = f2.apply(&mut classic::unstable::extend_quantifier_scope)
            .apply(&mut intuitionistic::remove_orphaned_variables)
            .apply(&mut intuitionistic::remove_empty_quantifications);
        formulas.push((f2.clone(), "extend_quantifier_scope".to_string()));

        f2 = f2.apply(&mut classic::unstable::simplify_transitive_equality)
            .apply(&mut intuitionistic::remove_orphaned_variables)
            .apply(&mut intuitionistic::remove_empty_quantifications);
        formulas.push((f2.clone(), "simplify_transitive_equality".to_string()));

        if f1 == f2 {
            break;
        }
        f1 = f2;
    }

    let mut problems = vec![];

    for i in 0..(formulas.len() - 1) {
        let axiom = formulas[i].clone().0;
        let (conjecture, simplification) = formulas[i + 1].clone();
        let name = format!("problem_{}_{}", simplification, i);
        let problem = Problem::with_name(name)
            .add_theory(axiom.into(), |i, formula| AnnotatedFormula {
                name: format!("axiom_{i}"),
                role: Role::Axiom,
                formula,
            })
            .add_theory(conjecture.into(), |i, formula| AnnotatedFormula {
                name: format!("conjecture_{i}"),
                role: Role::Conjecture,
                formula,
            })
            .rename_conflicting_symbols()
            .create_unique_formula_names();

        problems.push(problem);
    }

    problems
}
