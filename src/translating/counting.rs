// Helper functions for counting aggregates

use indexmap::IndexSet;

use crate::{
    syntax_tree::{
        asp::{self, AggregateAtom},
        fol::{self, BinaryConnective, Formula, Quantification, Quantifier},
    },
    translating::tau_star::{choose_fresh_variable_names, tau_b, val},
};

// For a mini-gringo program, tau-star produces a theory corresponding to a program
// But for mgc program, such a theory is only valid in the presence of supporting axioms
pub struct TargetTheory {
    pub formulas: Vec<Formula>,
    pub axioms: Vec<Formula>,
}

// Produces formula corresponding to atom Atleast_F^{X;V}(V,Z)
// and supporting axioms for Start and definitions of Atleast_F^{X;V}(V,Z)
fn at_least(
    x: IndexSet<asp::Variable>,
    v: IndexSet<asp::Variable>,
    f: fol::Formula,
    z: fol::Variable,
) -> TargetTheory {
    todo!()
}

// Produces formula corresponding to atom Atmost_F^{X;V}(V,Z)
// and supporting axioms for Start and definitions of Atmost_F^{X;V}(V,Z)
fn at_most(
    x: IndexSet<asp::Variable>,
    v: IndexSet<asp::Variable>,
    f: fol::Formula,
    z: fol::Variable,
) -> TargetTheory {
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
        name: choose_fresh_variable_names(&taken_vars, "C", 1)
            .pop()
            .unwrap(),
        sort: fol::Sort::General,
    };

    let x = IndexSet::from_iter(atom.aggregate.variable_list.iter().cloned());
    let v = globals
        .intersection(&atom.aggregate.condition_variables())
        .cloned()
        .collect();

    let mut w = vec![];
    for formula in atom.aggregate.conditions.iter() {
        for variable in formula.variables() {
            if !globals.contains(&variable) && !atom.aggregate.variable_list.contains(&variable) {
                w.push(fol::Variable {
                    name: variable.0,
                    sort: fol::Sort::General,
                });
            }
        }
    }

    let translated_conditions: Vec<Formula> = atom
        .aggregate
        .conditions
        .into_iter()
        .map(|f| {
            let theory = tau_b(f);
            fol::Formula::conjoin(theory.formulas)
        })
        .collect();

    let f = Formula::QuantifiedFormula {
        quantification: Quantification {
            quantifier: Quantifier::Exists,
            variables: w,
        },
        formula: fol::Formula::conjoin(translated_conditions).into(),
    };

    let count_theory = match atom.relation {
        asp::Relation::LessEqual => at_most(x, v, f, z.clone()),
        asp::Relation::GreaterEqual => at_least(x, v, f, z.clone()),
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
