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

enum At {
    Most,
    Least,
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

// corresponds to Ind schema for f
// Creates an induction shema using the first free integer variable of f
pub(crate) fn induction_schema(f: Formula) -> Formula {
    let free_vars = f.free_variables();

    let mut int_vars_of_f = free_vars
        .iter()
        .filter(|&v| matches!(v.sort, fol::Sort::Integer));

    match int_vars_of_f.next() {
        Some(var) => {
            let n = var.clone();
            let f_zero = f
                .clone()
                .substitute(n.clone(), GeneralTerm::IntegerTerm(IntegerTerm::Numeral(0)));

            let f_n_plus_1 = f.clone().substitute(
                n.clone(),
                GeneralTerm::IntegerTerm(IntegerTerm::BinaryOperation {
                    op: fol::BinaryOperator::Add,
                    lhs: IntegerTerm::Variable(n.name.clone()).into(),
                    rhs: IntegerTerm::Numeral(1).into(),
                }),
            );

            // forall N
            let forall_n = Quantification {
                quantifier: Quantifier::Forall,
                variables: vec![n.clone()],
            };

            // N >= 0
            let n_geq_zero =
                Formula::AtomicFormula(fol::AtomicFormula::Comparison(fol::Comparison {
                    term: GeneralTerm::IntegerTerm(IntegerTerm::Variable(n.name)),
                    guards: vec![Guard {
                        relation: fol::Relation::GreaterEqual,
                        term: GeneralTerm::IntegerTerm(IntegerTerm::Numeral(0)),
                    }],
                }));

            // F_0^N & forall N ( N >= 0 & F -> F_{N+1}^N )
            let induction_antecedent = Formula::BinaryFormula {
                connective: BinaryConnective::Conjunction,
                lhs: f_zero.into(),
                rhs: Formula::QuantifiedFormula {
                    quantification: forall_n.clone(),
                    formula: Formula::BinaryFormula {
                        connective: fol::BinaryConnective::Implication,
                        lhs: Formula::BinaryFormula {
                            connective: fol::BinaryConnective::Conjunction,
                            lhs: n_geq_zero.clone().into(),
                            rhs: f.clone().into(),
                        }
                        .into(),
                        rhs: f_n_plus_1.into(),
                    }
                    .into(),
                }
                .into(),
            };

            // forall N (N >= 0 -> F)
            let induction_consequent = Formula::QuantifiedFormula {
                quantification: forall_n,
                formula: Formula::BinaryFormula {
                    connective: BinaryConnective::Implication,
                    lhs: n_geq_zero.into(),
                    rhs: f.clone().into(),
                }
                .into(),
            };

            Formula::BinaryFormula {
                connective: fol::BinaryConnective::Implication,
                lhs: induction_antecedent.into(),
                rhs: induction_consequent.into(),
            }
            .universal_closure()
        }

        None => f,
    }
}

// Produces formula corresponding to atom Atmost_F^{X;V}(V,Z)
// and supporting axioms for Start and definitions of Atmost_F^{X;V}(V,Z)
fn at_most_at_least(
    x: IndexSet<asp::Variable>,
    v: IndexSet<asp::Variable>,
    f: fol::Formula,
    z: fol::Variable,
    id: usize,
    at: At,
) -> TargetTheory {
    let predicate_symbol = match at {
        At::Most => format!("at_most_f{id}"),
        At::Least => format!("at_least_f{id}"),
    };

    let mut atom_terms: Vec<GeneralTerm> = v
        .clone()
        .iter()
        .map(|v| GeneralTerm::Variable(v.0.clone()))
        .collect();

    let z_term: GeneralTerm = z.clone().into();
    atom_terms.push(z_term.clone());

    // Atmost_F^{X;V}(V,Z)
    // Atleast_F^{X;V}(V,Z)
    let at_atom = Formula::AtomicFormula(fol::AtomicFormula::Atom(fol::Atom {
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

    let mut axioms = vec![];

    // Ind for Start_F^{X;V}(X,V,N)
    let _start_ind = induction_schema(start_atom.clone());
    //axioms.push(_start_ind);

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

    // Atmost:  forall X N ( Start_F^{X;V}(X,V,N) -> N <= Z )
    // Atleast: exists X N ( Start_F^{X;V}(X,V,N) &  N >= Z )
    let at_definition_rhs = Formula::QuantifiedFormula {
        quantification: Quantification {
            quantifier: match at {
                At::Most => Quantifier::Forall,
                At::Least => Quantifier::Exists,
            },
            variables: x_n,
        },
        formula: Formula::BinaryFormula {
            connective: match at {
                At::Most => BinaryConnective::Implication,
                At::Least => BinaryConnective::Conjunction,
            },
            lhs: start_atom.into(),
            rhs: Formula::AtomicFormula(fol::AtomicFormula::Comparison(fol::Comparison {
                term: n_term,
                guards: vec![fol::Guard {
                    relation: match at {
                        At::Most => fol::Relation::LessEqual,
                        At::Least => fol::Relation::GreaterEqual,
                    },
                    term: z_term,
                }],
            }))
            .into(),
        }
        .into(),
    };

    // Atmost:  forall V Z ( Atmost_F^{X;V}(V,Z)  <-> at_definition_rhs )
    // Atleast: forall V Z ( Atleast_F^{X;V}(V,Z) <-> at_definition_rhs )
    let at_definition = Formula::QuantifiedFormula {
        quantification: Quantification {
            quantifier: Quantifier::Forall,
            variables,
        },
        formula: Formula::BinaryFormula {
            connective: BinaryConnective::Equivalence,
            lhs: at_atom.clone().into(),
            rhs: at_definition_rhs.into(),
        }
        .into(),
    };

    axioms.push(at_definition);
    axioms.append(&mut start_theory.axioms);

    TargetTheory {
        formulas: vec![at_atom],
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
            variables: atom.aggregate.variable_list.clone(),
            conditions: atom.aggregate.conditions.clone(),
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

    let f = if !w.is_empty() {
        Formula::QuantifiedFormula {
            quantification: Quantification {
                quantifier: Quantifier::Exists,
                variables: w,
            },
            formula: Formula::conjoin(translated_conditions).into(),
        }
    } else {
        Formula::conjoin(translated_conditions)
    };

    let count_theory = match atom.relation {
        asp::Relation::LessEqual => {
            at_most_at_least(x, v, f.clone(), z.clone(), formula_id, At::Most)
        }
        asp::Relation::GreaterEqual => {
            at_most_at_least(x, v, f.clone(), z.clone(), formula_id, At::Least)
        }
        _ => unreachable!(
            "cannot apply tau-star to an aggregate atom with relation {}",
            atom.relation
        ),
    };

    let count_theory_formula = Formula::conjoin(count_theory.formulas);

    // TODO: which formulas do we need to generate induction schema for?
    // count_theory
    //     .axioms
    //     .push(induction_schema(count_theory_formula.clone()));

    TargetTheory {
        formulas: vec![Formula::QuantifiedFormula {
            quantification: Quantification {
                quantifier: Quantifier::Exists,
                variables: vec![z.clone()],
            },
            formula: Formula::BinaryFormula {
                connective: BinaryConnective::Conjunction,
                lhs: val(atom.guard, z).into(),
                rhs: count_theory_formula.into(),
            }
            .into(),
        }],
        axioms: count_theory.axioms,
    }
}

#[cfg(test)]
mod tests {
    use {
        super::{At, at_most_at_least, induction_schema, start},
        crate::syntax_tree::{asp, fol},
        indexmap::IndexSet,
        std::iter::zip,
    };

    #[test]
    fn test_induction() {
        for (src, target) in [
            (
                "start_f1(X, V, N$i)",
                "forall X V (start_f1(X, V, 0) and forall N$i (N$i >= 0 and start_f1(X, V, N$i) -> start_f1(X, V, N$i+1)) -> forall N$i (N$i >= 0 -> start_f1(X, V, N$i)))",
            ),
            (
                "start_f1(X, V, N) and exists N$i p(N$i)",
                "start_f1(X, V, N) and exists N$i p(N$i)",
            ),
        ] {
            let left: fol::Formula = induction_schema(src.parse().unwrap());
            let right: fol::Formula = target.parse().unwrap();

            assert!(
                left == right,
                "assertion `left == right` failed:\n left:\n{left}\n right:\n{right}"
            );
        }
    }

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
            [
                //"forall S T V1 (start_f3(S, T, V1, 0) and forall N$i (N$i >= 0 and start_f3(S, T, V1, N$i) -> start_f3(S, T, V1, N$i + 1)) -> forall N$i (N$i >= 0 -> start_f3(S, T, V1, N$i)))",
                "forall V1 Z ( at_most_f3(V1,Z) <-> forall S T N$i (start_f3(S,T,V1,N$i) -> N$i <= Z) )",
            ],
        )] {
            let x: IndexSet<asp::Variable> =
                IndexSet::from_iter(x.into_iter().map(|v| v.parse().unwrap()));
            let v: IndexSet<asp::Variable> =
                IndexSet::from_iter(v.into_iter().map(|v| v.parse().unwrap()));
            let f: fol::Formula = f.parse().unwrap();
            let z: fol::Variable = z.parse().unwrap();
            let right_atom: fol::Formula = target_atom.parse().unwrap();

            let mut target_theory = at_most_at_least(x, v, f, z, id, At::Most);

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

    // #[test]
    // fn test_tau_b_formula() {
    //     let agg1 = AggregateFormulaKey {
    //         atom: "#count{ X : p(X,Y) } <= 2".parse().unwrap(),
    //         globals: vec!["Y".parse().unwrap()],
    //     };

    //     let agg2 = AggregateFormulaKey {
    //         atom: "#count{ X : p(X,Y) } <= 2".parse().unwrap(),
    //         globals: vec![],
    //     };

    //     let agg3 = AggregateFormulaKey {
    //         atom: "#count{ X : p(X) } >= Y".parse().unwrap(),
    //         globals: vec!["Y".parse().unwrap()],
    //     };

    //     let mut map = AggregateNameMap::new();
    //     map.insert(agg1, 1);
    //     map.insert(agg2, 2);
    //     map.insert(agg3, 3);

    //     for (atom, globals, target) in [
    //         (
    //             "#count{ X : p(X,Y) } <= 2",
    //             Some(["Y"]),
    //             "exists C (C = 2 and at_most_f1(Y,C))",
    //         ),
    //         (
    //             "#count{ X : p(X,Y) } <= 2",
    //             None,
    //             "exists C (C = 2 and at_most_f2(C))",
    //         ),
    //         (
    //             "#count{ X : p(X) } >= Y",
    //             Some(["Y"]),
    //             "exists C (C = Y and at_least_f3(C))",
    //         ),
    //     ] {
    //         let atom: AggregateAtom = atom.parse().unwrap();
    //         let globals: IndexSet<asp::Variable> = match globals {
    //             Some(vars) => IndexSet::from_iter(vars.into_iter().map(|v| v.parse().unwrap())),
    //             None => IndexSet::new(),
    //         };

    //         let left = tau_b_counting_atom(atom, &globals, &map)
    //             .formulas
    //             .pop()
    //             .unwrap();
    //         let right: fol::Formula = target.parse().unwrap();

    //         assert!(
    //             left == right,
    //             "assertion `left == right` failed:\n left:\n{left}\n right:\n{right}"
    //         );
    //     }
    // }

    // #[test]
    // fn test_tau_b_axioms() {
    //     let agg1 = AggregateFormulaKey {
    //         atom: "#count{ X : p(X,Y) } <= 2".parse().unwrap(),
    //         globals: vec!["Y".parse().unwrap()],
    //     };

    //     let mut map = AggregateNameMap::new();
    //     map.insert(agg1, 1);

    //     for (atom, globals, target) in [
    //         (
    //             "#count{ X : p(X,Y) } <= 2",
    //             Some(["Y"]),
    //             "forall X Y N$i (N$i <= 0 -> start_f1(X, Y, N$i)).
    //             forall X Y (start_f1(X, Y, 1) <-> exists Z Z1 (Z = X and Z1 = Y and p(Z,Z1)) ).
    //             forall X Y N$i ( N$i > 0 -> (start_f1(X, Y, N$i+1) <-> exists Z Z1 (Z = X and Z1 = Y and p(Z,Z1)) and exists U (X < U and start_f1(U,Y,N$i)) ) ).
    //             forall Y C ( at_most_f1(Y,C) <-> forall X N$i (start_f1(X,Y,N$i) -> N$i <= C) ).
    //             forall X Y (start_f1(X, Y, 0) and forall N$i (N$i >= 0 and start_f1(X, Y, N$i) -> start_f1(X, Y, N$i+1)) -> forall N$i (N$i >= 0 -> start_f1(X, Y, N$i))).",
    //         ),
    //     ] {
    //         let atom: AggregateAtom = atom.parse().unwrap();
    //         let globals: IndexSet<asp::Variable> = match globals {
    //             Some(vars) => IndexSet::from_iter(vars.into_iter().map(|v| v.parse().unwrap())),
    //             None => IndexSet::new(),
    //         };

    //         let mut left_formulas = tau_b_counting_atom(atom, &globals, &map).axioms;
    //         left_formulas.sort();

    //         let right_theory: fol::Theory = target.parse().unwrap();
    //         let mut right_formulas = right_theory.formulas;
    //         right_formulas.sort();

    //         let left = fol::Theory {
    //             formulas: left_formulas,
    //         };
    //         let right = fol::Theory {
    //             formulas: right_formulas,
    //         };
    //         assert!(
    //             left == right,
    //             "assertion `left == right` failed:\n left:\n{left}\n right:\n{right}"
    //         );
    //     }
    // }
}
