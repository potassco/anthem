// Helper functions for counting aggregates

use indexmap::IndexSet;

use crate::{
    convenience::{apply::Apply, compose::Compose as _},
    simplifying::fol::intuitionistic::BASIC,
    syntax_tree::{
        asp::{self, AggregateAtom, AggregateFormulaKey, AggregateNameMap},
        fol::{
            self, BinaryConnective, Formula, GeneralTerm, Guard, IntegerTerm, Quantification,
            Quantifier,
        },
    },
    translating::tau_star::{choose_fresh_variable_names, tau_b, val},
};

// // Choose a variation of variant such that a variable with the chosen name does not occur in formula
// fn choose_fresh_variable_for_formula(formula: &Formula, variant: &str) -> String {
//     let taken_variables = formula.variables();
//     let var = choose_fresh_variable_names(&taken_variables, variant, 1)
//         .pop()
//         .unwrap();
//     var
// }

// For a mini-gringo program, tau-star produces a theory corresponding to a program
// But for mgc program, such a theory is only valid in the presence of supporting axioms
pub struct TargetTheory {
    pub formulas: Vec<Formula>,
    pub axioms: Vec<Formula>,
}

// Conjoins all formulas up to but excluding formula[bound]
// bigwedge_{k=0}^{bound-1}( Xk = Uk )
fn conjunction_function(formulas: &[Formula], bound: usize) -> Formula {
    let mut formulas_slice = Vec::new();

    for formula in formulas.iter().take(bound) {
        formulas_slice.push(formula.clone());
    }

    Formula::conjoin(formulas_slice)
}

// X < U
fn lexicographic_order(x: Vec<fol::Variable>, u: Vec<fol::Variable>) -> Formula {
    let m = x.len();

    let x_terms: Vec<GeneralTerm> = x
        .into_iter()
        .map(|v| GeneralTerm::Variable(v.name))
        .collect();
    let u_terms: Vec<GeneralTerm> = u
        .into_iter()
        .map(|v| GeneralTerm::Variable(v.name))
        .collect();

    // x_equals_u[k] is the formula Xk = Uk
    let mut x_equals_u = Vec::new();
    for i in 0..m {
        x_equals_u.push(Formula::AtomicFormula(fol::AtomicFormula::Comparison(
            fol::Comparison {
                term: x_terms[i].clone(),
                guards: vec![Guard {
                    relation: fol::Relation::Equal,
                    term: u_terms[i].clone(),
                }],
            },
        )));
    }

    // x_less_u[l] is the formula Xl = Ul
    let mut x_less_u = Vec::new();
    for i in 0..m {
        x_less_u.push(Formula::AtomicFormula(fol::AtomicFormula::Comparison(
            fol::Comparison {
                term: x_terms[i].clone(),
                guards: vec![Guard {
                    relation: fol::Relation::Less,
                    term: u_terms[i].clone(),
                }],
            },
        )));
    }

    let mut formulas = Vec::new();
    for (l, less_formula) in x_less_u.iter().enumerate() {
        formulas.push(Formula::BinaryFormula {
            connective: fol::BinaryConnective::Conjunction,
            lhs: less_formula.clone().into(),
            rhs: conjunction_function(&x_equals_u, l).into(),
        })
    }

    Formula::disjoin(formulas)
}

// exists U ( X < U & Start_F^{X;V}(U,V,N) )
fn start_helper(
    x: &IndexSet<fol::Variable>,
    v: &IndexSet<fol::Variable>,
    n: &fol::Variable,
    predicate_symbol: String,
) -> Formula {
    let arity = x.len();

    let mut taken_variables = x.clone();
    taken_variables.extend(v.clone());
    taken_variables.insert(n.clone());

    let u_names = choose_fresh_variable_names(&taken_variables, "U", arity);
    let u_vars: Vec<fol::Variable> = u_names
        .iter()
        .map(|name| fol::Variable {
            name: name.clone(),
            sort: fol::Sort::General,
        })
        .collect();
    let u_terms = u_names.into_iter().map(GeneralTerm::Variable).collect();

    let x_vars: Vec<fol::Variable> = x
        .iter()
        .map(|v| fol::Variable {
            name: v.name.clone(),
            sort: fol::Sort::General,
        })
        .collect();
    let v_terms: Vec<GeneralTerm> = v
        .iter()
        .map(|v| GeneralTerm::Variable(v.name.clone()))
        .collect();
    let n_term = GeneralTerm::IntegerTerm(IntegerTerm::Variable(n.name.clone()));

    let mut u_v_n: Vec<GeneralTerm> = u_terms;
    u_v_n.extend(v_terms.clone());
    u_v_n.push(n_term);

    Formula::QuantifiedFormula {
        quantification: Quantification {
            quantifier: Quantifier::Exists,
            variables: u_vars.clone(),
        },
        formula: Formula::BinaryFormula {
            connective: BinaryConnective::Conjunction,
            lhs: lexicographic_order(x_vars, u_vars).into(),
            rhs: Formula::AtomicFormula(fol::AtomicFormula::Atom(fol::Atom {
                predicate_symbol,
                terms: u_v_n,
            }))
            .into(),
        }
        .into(),
    }
    .apply_fixpoint(&mut [BASIC].concat().into_iter().compose())
}

// Produces formula corresponding to atom Start_F^{X;V}(X,V,N)
// and supporting axioms D0 for Start
fn start(
    x: IndexSet<asp::Variable>,
    v: IndexSet<asp::Variable>,
    f: fol::Formula,
    id: usize,
) -> TargetTheory {
    let start_predicate_symbol = format!("start_f{id}");

    let mut start_terms: Vec<GeneralTerm> = x
        .iter()
        .map(|v| GeneralTerm::Variable(v.0.clone()))
        .collect();
    start_terms.extend(v.iter().map(|v| GeneralTerm::Variable(v.0.clone())));

    // X
    let x_vars: IndexSet<fol::Variable> = IndexSet::from_iter(x.iter().map(|v| fol::Variable {
        name: v.0.clone(),
        sort: fol::Sort::General,
    }));

    // V
    let v_vars: IndexSet<fol::Variable> = IndexSet::from_iter(v.iter().map(|v| fol::Variable {
        name: v.0.clone(),
        sort: fol::Sort::General,
    }));

    let mut taken_variables = x_vars.clone();
    taken_variables.extend(v_vars.clone());
    taken_variables.extend(f.variables());

    // N
    let n = fol::Variable {
        name: choose_fresh_variable_names(&taken_variables, "N", 1)
            .pop()
            .unwrap(),
        sort: fol::Sort::Integer,
    };

    // exists U ( X < U & Start_F^{X;V}(U,V,N) )
    let minimize_formula = start_helper(&x_vars, &v_vars, &n, start_predicate_symbol.clone());

    // X, V (as variables)
    let mut variables = Vec::new();
    variables.extend(x_vars);
    variables.extend(v_vars);

    // X, V, 1 (as terms)
    let mut start_terms_1 = start_terms.clone();
    start_terms_1.push(GeneralTerm::IntegerTerm(IntegerTerm::Numeral(1)));

    // forall X V ( Start_F^{X;V}(X,V,1) <-> F )
    let start_iff_f = Formula::QuantifiedFormula {
        quantification: Quantification {
            quantifier: Quantifier::Forall,
            variables: variables.clone(),
        },
        formula: Formula::BinaryFormula {
            connective: fol::BinaryConnective::Equivalence,
            lhs: Formula::AtomicFormula(fol::AtomicFormula::Atom(fol::Atom {
                predicate_symbol: start_predicate_symbol.clone(),
                terms: start_terms_1,
            }))
            .into(),
            rhs: f.clone().into(),
        }
        .into(),
    };

    // X, V, N (as variables)
    variables.push(n.clone());

    // X, V, N (as terms)
    let n_term = GeneralTerm::IntegerTerm(IntegerTerm::Variable(n.name.clone()));
    let mut start_terms_n = start_terms.clone();
    start_terms_n.push(n_term.clone());

    // forall X V N
    let forall_x_v_n = Quantification {
        quantifier: Quantifier::Forall,
        variables,
    };

    // Start_F^{X;V}(X,V,N)
    let start_atom_n = Formula::AtomicFormula(fol::AtomicFormula::Atom(fol::Atom {
        predicate_symbol: start_predicate_symbol.clone(),
        terms: start_terms_n,
    }));

    // forall X V N ( N <= 0 -> Start_F^{X;V}(X,V,N) )
    let start_n_leq_zero = Formula::QuantifiedFormula {
        quantification: forall_x_v_n.clone(),
        formula: Formula::BinaryFormula {
            connective: BinaryConnective::Implication,
            lhs: Formula::AtomicFormula(fol::AtomicFormula::Comparison(fol::Comparison {
                term: n_term.clone(),
                guards: vec![Guard {
                    relation: fol::Relation::LessEqual,
                    term: GeneralTerm::IntegerTerm(IntegerTerm::Numeral(0)),
                }],
            }))
            .into(),
            rhs: start_atom_n.clone().into(),
        }
        .into(),
    };

    // Start_F^{X;V}(X,V,N+1)
    let mut start_terms_n_plus_one = start_terms.clone();
    start_terms_n_plus_one.push(GeneralTerm::IntegerTerm(IntegerTerm::BinaryOperation {
        op: fol::BinaryOperator::Add,
        lhs: IntegerTerm::Variable(n.name).into(),
        rhs: IntegerTerm::Numeral(1).into(),
    }));
    let start_n_plus_one = Formula::AtomicFormula(fol::AtomicFormula::Atom(fol::Atom {
        predicate_symbol: start_predicate_symbol,
        terms: start_terms_n_plus_one,
    }));

    // F & exists U ( X < U & Start_F^{X;V}(U,V,N) ) )
    let f_and_exists_u = Formula::BinaryFormula {
        connective: fol::BinaryConnective::Conjunction,
        lhs: f.into(),
        rhs: minimize_formula.into(),
    };

    // forall X V N ( N > 0 -> ( Start_F^{X;V}(X,V,N+1) <-> F & exists U ( X < U & Start_F^{X;V}(U,V,N) ) ) )
    let start_n_greater_zero = Formula::QuantifiedFormula {
        quantification: forall_x_v_n,
        formula: Formula::BinaryFormula {
            connective: fol::BinaryConnective::Implication,
            lhs: Formula::AtomicFormula(fol::AtomicFormula::Comparison(fol::Comparison {
                term: n_term,
                guards: vec![Guard {
                    relation: fol::Relation::Greater,
                    term: GeneralTerm::IntegerTerm(IntegerTerm::Numeral(0)),
                }],
            }))
            .into(),
            rhs: Formula::BinaryFormula {
                connective: fol::BinaryConnective::Equivalence,
                lhs: start_n_plus_one.into(),
                rhs: f_and_exists_u.into(),
            }
            .into(),
        }
        .into(),
    };

    TargetTheory {
        formulas: vec![start_atom_n],
        axioms: vec![start_n_leq_zero, start_iff_f, start_n_greater_zero],
    }
}

// Produces formula corresponding to atom Atleast_F^{X;V}(V,Z)
// and supporting axioms for Start and definitions of Atleast_F^{X;V}(V,Z)
// fn at_least(
//     x: IndexSet<asp::Variable>,
//     v: IndexSet<asp::Variable>,
//     f: fol::Formula,
//     z: fol::Variable,
//     id: usize,
// ) -> TargetTheory {
//     let predicate_name = format!("at_least_f{id}");

//     let start_theory = start(x, v, f, id);

//     todo!()
// }

// // corresponds to Ind schemas
// fn induction(f: fol::Formula) -> Vec<Formula> {
//     todo!()
// }

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

    let mut atom_terms: Vec<GeneralTerm> = v
        .clone()
        .iter()
        .map(|v| GeneralTerm::Variable(v.0.clone()))
        .collect();

    let z_term: GeneralTerm = z.clone().into();
    atom_terms.push(z_term.clone());

    // Atmost_F^{X;V}(V,Z)
    let at_most_atom = Formula::AtomicFormula(fol::AtomicFormula::Atom(fol::Atom {
        predicate_symbol,
        terms: atom_terms,
    }));

    let mut start_theory = start(x.clone(), v.clone(), f, id);

    // V, Z
    let mut variables: Vec<fol::Variable> = v
        .clone()
        .iter()
        .map(|v| fol::Variable {
            name: v.0.clone(),
            sort: fol::Sort::General,
        })
        .collect();
    variables.push(z.clone());

    // Start_F^{X;V}(X,V,N)
    let start_atom = start_theory.formulas.pop().unwrap();

    // N
    let n = match start_atom.clone() {
        Formula::AtomicFormula(fol::AtomicFormula::Atom(a)) => {
            let n: fol::Variable = a
                .terms
                .last()
                .unwrap()
                .clone()
                .try_into()
                .expect("last term of start atom should be an integer variable");
            n
        }
        _ => panic!("bug! start atom was improperly defined"),
    };

    let mut x_n: Vec<fol::Variable> = x
        .iter()
        .map(|v| fol::Variable {
            name: v.0.clone(),
            sort: fol::Sort::General,
        })
        .collect();
    x_n.push(n.clone());

    let n_term: GeneralTerm = n.into();

    // forall X N ( Start_F^{X;V}(X,V,N) -> N <= Z )
    let forall_start = Formula::QuantifiedFormula {
        quantification: Quantification {
            quantifier: Quantifier::Forall,
            variables: x_n,
        },
        formula: Formula::BinaryFormula {
            connective: BinaryConnective::Implication,
            lhs: start_atom.into(),
            rhs: Formula::AtomicFormula(fol::AtomicFormula::Comparison(fol::Comparison {
                term: n_term,
                guards: vec![fol::Guard {
                    relation: fol::Relation::LessEqual,
                    term: z_term,
                }],
            }))
            .into(),
        }
        .into(),
    };

    // forall V Z ( Atmost_F^{X;V}(V,Z) <-> forall X N ( Start_F^{X;V}(X,V,N) -> N <= Z ) )
    let at_most_definition = Formula::QuantifiedFormula {
        quantification: Quantification {
            quantifier: Quantifier::Forall,
            variables,
        },
        formula: Formula::BinaryFormula {
            connective: BinaryConnective::Equivalence,
            lhs: at_most_atom.clone().into(),
            rhs: forall_start.into(),
        }
        .into(),
    };

    let mut axioms = vec![at_most_definition];
    axioms.append(&mut start_theory.axioms);

    TargetTheory {
        formulas: vec![at_most_atom],
        axioms,
    }
}

pub(crate) fn tau_b_counting_atom(
    atom: AggregateAtom,
    globals: &IndexSet<asp::Variable>,
    aggregate_names: &AggregateNameMap,
) -> TargetTheory {
    let global_vars = Vec::from_iter(globals.iter().cloned());
    let formula_id = *aggregate_names
        .get(&AggregateFormulaKey {
            atom: atom.clone(),
            globals: global_vars,
        })
        .unwrap();

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
        formula: Formula::conjoin(translated_conditions).into(),
    };

    let count_theory = match atom.relation {
        asp::Relation::LessEqual => at_most(x, v, f.clone(), z.clone(), formula_id),
        //asp::Relation::GreaterEqual => at_least(x, v, f.clone(), z.clone(), formula_id),      TODO
        _ => unreachable!(
            "cannot apply tau-star to an aggregate atom with relation {}",
            atom.relation
        ),
    };

    // TODO
    //count_theory.axioms.append(&mut induction(f));

    TargetTheory {
        formulas: vec![Formula::QuantifiedFormula {
            quantification: Quantification {
                quantifier: Quantifier::Exists,
                variables: vec![z.clone()],
            },
            formula: Formula::BinaryFormula {
                connective: BinaryConnective::Conjunction,
                lhs: val(atom.guard, z).into(),
                rhs: Formula::conjoin(count_theory.formulas).into(),
            }
            .into(),
        }],
        axioms: count_theory.axioms,
    }
}

#[cfg(test)]
mod tests {

    use std::iter::zip;

    use indexmap::IndexSet;

    use crate::syntax_tree::{asp, fol};

    use super::{at_most, start};

    // #[test]
    // fn test_choose_fresh_variable_for_formula() {
    //     for (formula, variant, target) in [
    //         ("p(Y)", "Y", "Y1"),
    //         ("forall Y (p(Y))", "X", "X"),
    //         ("forall X Y (p(Y))", "X", "X1"),
    //         ("N$i < 4 and exists X N1$i (X = N1$i + 1)", "N", "N2"),
    //     ] {
    //         let formula: fol::Formula = formula.parse().unwrap();
    //         let left = choose_fresh_variable_for_formula(&formula, variant);
    //         let right = target;

    //         assert!(
    //             left == right,
    //             "assertion `left == right` failed:\n left:\n{left}\n right:\n{right}"
    //         );
    //     }
    // }

    #[test]
    fn test_start() {
        for (x, v, f, id, target_atom, target_axioms) in [(
            ["S", "T"],
            ["V1"],
            "p(V1) and V1 = S or V1 = T",
            3,
            "start_f3(S, T, V1, N$i)",
            [
                "forall S T V1 N$i (N$i <= 0 -> start_f3(S, T, V1, N$i))",
                "forall S T V1 (start_f3(S, T, V1, 1) <-> (p(V1) and V1 = S or V1 = T) )",
                "forall S T V1 N$i ( N$i > 0 -> (start_f3(S, T, V1, N$i+1) <-> (p(V1) and V1 = S or V1 = T) and exists U U1 ( (S < U or (T < U1 and S = U)) and start_f3(U,U1,V1,N$i) )) )",
            ],
        )] {
            let x: IndexSet<asp::Variable> =
                IndexSet::from_iter(x.into_iter().map(|v| v.parse().unwrap()));
            let v: IndexSet<asp::Variable> =
                IndexSet::from_iter(v.into_iter().map(|v| v.parse().unwrap()));
            let f: fol::Formula = f.parse().unwrap();

            let right_atom: fol::Formula = target_atom.parse().unwrap();

            let mut target_theory = start(x, v, f, id);

            let left_atom = target_theory.formulas.pop().unwrap();

            assert!(
                left_atom == right_atom,
                "assertion `left == right` failed:\n left:\n{left_atom}\n right:\n{right_atom}"
            );

            let axioms: Vec<fol::Formula> = target_axioms
                .into_iter()
                .map(|f| f.parse().unwrap())
                .collect();

            let mut axiom_iter = zip(target_theory.axioms, axioms).peekable();

            while axiom_iter.peek().is_some() {
                let (left_axiom, right_axiom) = axiom_iter.next().unwrap();
                assert!(
                    left_axiom == right_axiom,
                    "assertion `left == right` failed:\n left:\n{left_axiom}\n right:\n{right_axiom}"
                );
            }
        }
    }

    #[test]
    fn test_at_most() {
        for (x, v, f, z, id, target_atom, target_axioms) in [(
            ["S", "T"],
            ["V1"],
            "p(V1) and V1 = S or V1 = T",
            "Z",
            3,
            "at_most_f3(V1, Z)",
            ["forall V1 Z ( at_most_f3(V1,Z) <-> forall S T N$i (start_f3(S,T,V1,N$i) -> N$i <= Z) )"],
        )] {
            let x: IndexSet<asp::Variable> =
                IndexSet::from_iter(x.into_iter().map(|v| v.parse().unwrap()));
            let v: IndexSet<asp::Variable> =
                IndexSet::from_iter(v.into_iter().map(|v| v.parse().unwrap()));
            let f: fol::Formula = f.parse().unwrap();
            let z: fol::Variable = z.parse().unwrap();
            let right_atom: fol::Formula = target_atom.parse().unwrap();

            let mut target_theory = at_most(x, v, f, z, id);

            let left_atom = target_theory.formulas.pop().unwrap();

            assert!(
                left_atom == right_atom,
                "assertion `left == right` failed:\n left:\n{left_atom}\n right:\n{right_atom}"
            );

            let axioms: Vec<fol::Formula> = target_axioms
                .into_iter()
                .map(|f| f.parse().unwrap())
                .collect();

            let mut axiom_iter = zip(target_theory.axioms, axioms).peekable();

            while axiom_iter.peek().is_some() {
                let (left_axiom, right_axiom) = axiom_iter.next().unwrap();
                assert!(
                    left_axiom == right_axiom,
                    "assertion `left == right` failed:\n left:\n{left_axiom}\n right:\n{right_axiom}"
                );
            }
        }
    }
}
