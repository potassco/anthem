// Helper functions for counting aggregates

use indexmap::IndexSet;

use crate::{
    syntax_tree::{
        asp::{self, AggregateAtom},
        fol::{self, BinaryConnective, Formula, Quantification, Quantifier},
    },
    translating::tau_star::{choose_fresh_variable_names, val},
};

// For a mini-gringo program, tau-star produces a theory corresponding to a program
// But for mgc program, such a theory is only valid in the presence of supporting axioms
pub struct TargetTheory {
    pub formulas: Vec<Formula>,
    pub axioms: Vec<Formula>,
}

fn at_least() -> TargetTheory {
    todo!()
}

fn at_most() -> TargetTheory {
    todo!()
}

pub(crate) fn tau_b_counting_atom(
    atom: AggregateAtom,
    globals: &IndexSet<asp::Variable>,
) -> TargetTheory {
    let mut taken_vars = IndexSet::from_iter(globals.iter().cloned().map(|v| fol::Variable {
        name: v.0,
        sort: fol::Sort::General,
    }));
    for var in atom.variables().iter() {
        taken_vars.insert(fol::Variable {
            name: var.to_string(),
            sort: fol::Sort::General,
        });
    }
    let z = fol::Variable {
        name: choose_fresh_variable_names(&taken_vars, "Z", 1)
            .pop()
            .unwrap(),
        sort: fol::Sort::General,
    };

    let count_theory = match atom.relation {
        asp::Relation::LessEqual => at_most(),
        asp::Relation::GreaterEqual => at_least(),
        _ => unreachable!(
            "cannot apply tau-star to an aggregate atom with relation {}",
            atom.relation
        ),
    };

    TargetTheory {
        formulas: vec![Formula::QuantifiedFormula {
            quantification: Quantification {
                quantifier: Quantifier::Exists,
                variables: vec![z.clone()],
            },
            formula: Formula::BinaryFormula {
                connective: BinaryConnective::Conjunction,
                lhs: val(atom.guard, z).into(),
                rhs: fol::Formula::conjoin(count_theory.formulas).into(),
            }
            .into(),
        }],
        axioms: count_theory.axioms,
    }
}
