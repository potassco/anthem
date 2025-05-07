// Helper functions for counting aggregates

use indexmap::IndexSet;

use crate::{
    syntax_tree::{
        asp::{self, AggregateAtom, AggregateFormulaKey, AggregateNameMap},
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

// Produces formula corresponding to atom Start_F^{X;V}
// and supporting axioms for Start
fn start(
    x: IndexSet<asp::Variable>,
    v: IndexSet<asp::Variable>,
    f: fol::Formula,
    id: usize,
) -> TargetTheory {
    let start_predicate_symbol = format!("start_f{id}");
    let mut start_terms = x.iter().map(|v| {
        fol::GeneralTerm::Variable(v.0.clone())
    }).collect();

    todo!()
}

// Produces formula corresponding to atom Atleast_F^{X;V}(V,Z)
// and supporting axioms for Start and definitions of Atleast_F^{X;V}(V,Z)
fn at_least(
    x: IndexSet<asp::Variable>,
    v: IndexSet<asp::Variable>,
    f: fol::Formula,
    z: fol::Variable,
    id: usize,
) -> TargetTheory {
    let predicate_name = format!("at_least_f{id}");

    let start_theory = start(x, v, f, id);

    todo!()
}

// corresponds to Ind schemas
fn induction(f: fol::Formula) -> Vec<Formula> {
    todo!()
}

// Produces formula corresponding to atom Atmost_F^{X;V}(V,Z)
// and supporting axioms for Start and definitions of Atmost_F^{X;V}(V,Z)
fn at_most(
    x: IndexSet<asp::Variable>,
    v: IndexSet<asp::Variable>,
    f: fol::Formula,
    z: fol::Variable,
    id: usize,
) -> TargetTheory {
    let predicate_symbol = format!("at_most_f{id}");
    let terms = v.clone().iter().map(|v| {
        fol::GeneralTerm::Variable(v.0.clone())
    }).collect();

    let at_most_atom = Formula::AtomicFormula(fol::AtomicFormula::Atom(fol::Atom {
        predicate_symbol,
        terms,
    }));

    let mut start_theory = start(x, v.clone(), f, id);

    let mut variables: Vec<fol::Variable> = v.clone().iter().map(|v| {
        fol::Variable {
            name: v.0.clone(),
            sort: fol::Sort::General,
        }
    }).collect();
    variables.push(z);

    let forall_start = Formula::QuantifiedFormula { quantification: todo!(), formula: todo!() };

    let at_most_definition = Formula::QuantifiedFormula {
        quantification: Quantification { quantifier: Quantifier::Forall, variables },
        formula: Formula::BinaryFormula {
            connective: BinaryConnective::Equivalence,
            lhs: at_most_atom.into(),
            rhs: forall_start.into(),
        }.into()
    };

    let mut axioms = vec![at_most_definition];
    axioms.append(&mut start_theory.axioms);

    TargetTheory { formulas: vec![at_most_atom], axioms }
}

pub(crate) fn tau_b_counting_atom(
    atom: AggregateAtom,
    globals: &IndexSet<asp::Variable>,
    aggregate_names: &AggregateNameMap,
) -> TargetTheory {
    let global_vars = Vec::from_iter(globals.iter().cloned());
    let formula_id = aggregate_names
        .get(&AggregateFormulaKey {
            atom: atom.clone(),
            globals: global_vars,
        })
        .unwrap()
        .clone();

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

    let mut count_theory = match atom.relation {
        asp::Relation::LessEqual => at_most(x, v, f.clone(), z.clone(), formula_id),
        asp::Relation::GreaterEqual => at_least(x, v, f.clone(), z.clone(), formula_id),
        _ => unreachable!(
            "cannot apply tau-star to an aggregate atom with relation {}",
            atom.relation
        ),
    };

    count_theory.axioms.append(&mut induction(f));

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
