use indexmap::{IndexMap, IndexSet};

use crate::{
    syntax_tree::{
        asp,
        asp::mini_gringo::{Program, Rule},
        fol,
        fol::{Formula, GeneralTerm, Guard, IntegerTerm, Quantification, Quantifier},
    },
    translating::tau_star::{
        choose_fresh_global_variables, choose_fresh_variable_names,
        construct_absolute_value_formula, construct_equality_formula, construct_interval_formula,
        construct_total_function_formula, tau_body,
    },
};

pub(crate) fn choose_fresh_ijk(
    taken_variables: &IndexSet<fol::Variable>,
) -> IndexMap<&str, fol::Variable> {
    let mut fresh_ivar = choose_fresh_variable_names(taken_variables, "I", 1);
    let mut fresh_jvar = choose_fresh_variable_names(taken_variables, "J", 1);
    let mut fresh_kvar = choose_fresh_variable_names(taken_variables, "K", 1);

    let mut fresh_int_vars = IndexMap::new();

    fresh_int_vars.insert(
        "I",
        fol::Variable {
            name: fresh_ivar.pop().unwrap(),
            sort: fol::Sort::Integer,
        },
    );
    fresh_int_vars.insert(
        "J",
        fol::Variable {
            name: fresh_jvar.pop().unwrap(),
            sort: fol::Sort::Integer,
        },
    );
    fresh_int_vars.insert(
        "K",
        fol::Variable {
            name: fresh_kvar.pop().unwrap(),
            sort: fol::Sort::Integer,
        },
    );

    fresh_int_vars
}

// I,J,K must be integer variables
// K * |J| <= |I| < (K+1) * |J|
fn division_helper_f1(i: fol::Variable, j: fol::Variable, k: fol::Variable) -> Formula {
    // K * |J|
    let term1 = GeneralTerm::IntegerTerm(IntegerTerm::BinaryOperation {
        op: fol::BinaryOperator::Multiply,
        lhs: IntegerTerm::Variable(k.name.clone()).into(),
        rhs: IntegerTerm::UnaryOperation {
            op: fol::UnaryOperator::AbsoluteValue,
            arg: IntegerTerm::Variable(j.name.clone()).into(),
        }
        .into(),
    });

    // |I|
    let term2 = GeneralTerm::IntegerTerm(IntegerTerm::UnaryOperation {
        op: fol::UnaryOperator::AbsoluteValue,
        arg: IntegerTerm::Variable(i.name.clone()).into(),
    });

    // (K+1) * |J|
    let term3 = GeneralTerm::IntegerTerm(IntegerTerm::BinaryOperation {
        op: fol::BinaryOperator::Multiply,
        lhs: IntegerTerm::BinaryOperation {
            op: fol::BinaryOperator::Add,
            lhs: IntegerTerm::Variable(k.name.clone()).into(),
            rhs: IntegerTerm::Numeral(1).into(),
        }
        .into(),
        rhs: IntegerTerm::UnaryOperation {
            op: fol::UnaryOperator::AbsoluteValue,
            arg: IntegerTerm::Variable(j.name.clone()).into(),
        }
        .into(),
    });

    Formula::AtomicFormula(fol::AtomicFormula::Comparison(fol::Comparison {
        term: term1,
        guards: vec![
            Guard {
                relation: fol::Relation::LessEqual,
                term: term2,
            },
            Guard {
                relation: fol::Relation::Less,
                term: term3,
            },
        ],
    }))
}

// (I * J >= 0 & Z = K) v (I * J < 0 & Z = -K)
fn division_helper_f2(
    i: fol::Variable, // Must be an integer variable
    j: fol::Variable, // Must be an integer variable
    k: fol::Variable, // Must be an integer variable
    z: fol::Variable, // Must be a general variable
) -> Formula {
    // I * J
    let i_times_j = GeneralTerm::IntegerTerm(IntegerTerm::BinaryOperation {
        op: fol::BinaryOperator::Multiply,
        lhs: IntegerTerm::Variable(i.name.clone()).into(),
        rhs: IntegerTerm::Variable(j.name.clone()).into(),
    });

    // I * J >= 0
    let ij_geq_zero = Formula::AtomicFormula(fol::AtomicFormula::Comparison(fol::Comparison {
        term: i_times_j.clone(),
        guards: vec![Guard {
            relation: fol::Relation::GreaterEqual,
            term: GeneralTerm::IntegerTerm(IntegerTerm::Numeral(0)),
        }],
    }));

    // Z = K
    let z_equals_k = Formula::AtomicFormula(fol::AtomicFormula::Comparison(fol::Comparison {
        term: z.clone().into(),
        guards: vec![Guard {
            relation: fol::Relation::Equal,
            term: GeneralTerm::IntegerTerm(IntegerTerm::Variable(k.name.clone())),
        }],
    }));

    // I * J < 0
    let ij_less_zero = Formula::AtomicFormula(fol::AtomicFormula::Comparison(fol::Comparison {
        term: i_times_j,
        guards: vec![Guard {
            relation: fol::Relation::Less,
            term: GeneralTerm::IntegerTerm(IntegerTerm::Numeral(0)),
        }],
    }));

    // Z = -K
    let z_equals_neg_k = Formula::AtomicFormula(fol::AtomicFormula::Comparison(fol::Comparison {
        term: z.into(),
        guards: vec![Guard {
            relation: fol::Relation::Equal,
            term: GeneralTerm::IntegerTerm(IntegerTerm::UnaryOperation {
                op: fol::UnaryOperator::Negative,
                arg: IntegerTerm::Variable(k.name).into(),
            }),
        }],
    }));

    Formula::BinaryFormula {
        connective: fol::BinaryConnective::Disjunction,
        lhs: Formula::BinaryFormula {
            connective: fol::BinaryConnective::Conjunction,
            lhs: ij_geq_zero.into(),
            rhs: z_equals_k.into(),
        }
        .into(),
        rhs: Formula::BinaryFormula {
            connective: fol::BinaryConnective::Conjunction,
            lhs: ij_less_zero.into(),
            rhs: z_equals_neg_k.into(),
        }
        .into(),
    }
}

// (I * J >= 0 & Z = I - K * J) v (I * J < 0 & Z = I + K * J)
fn division_helper_f3(
    i: fol::Variable,
    j: fol::Variable,
    k: fol::Variable,
    z: fol::Variable,
) -> Formula {
    // I * J
    let i_times_j = GeneralTerm::IntegerTerm(IntegerTerm::BinaryOperation {
        op: fol::BinaryOperator::Multiply,
        lhs: IntegerTerm::Variable(i.name.clone()).into(),
        rhs: IntegerTerm::Variable(j.name.clone()).into(),
    });

    // I * J >= 0
    let ij_geq_zero = Formula::AtomicFormula(fol::AtomicFormula::Comparison(fol::Comparison {
        term: i_times_j.clone(),
        guards: vec![Guard {
            relation: fol::Relation::GreaterEqual,
            term: GeneralTerm::IntegerTerm(IntegerTerm::Numeral(0)),
        }],
    }));

    // I * J < 0
    let ij_less_zero = Formula::AtomicFormula(fol::AtomicFormula::Comparison(fol::Comparison {
        term: i_times_j,
        guards: vec![Guard {
            relation: fol::Relation::Less,
            term: GeneralTerm::IntegerTerm(IntegerTerm::Numeral(0)),
        }],
    }));

    // K * J
    let k_times_j = IntegerTerm::BinaryOperation {
        op: fol::BinaryOperator::Multiply,
        lhs: IntegerTerm::Variable(k.name.clone()).into(),
        rhs: IntegerTerm::Variable(j.name.clone()).into(),
    };

    // Z = I - K * J
    let z_equals_i_minus =
        Formula::AtomicFormula(fol::AtomicFormula::Comparison(fol::Comparison {
            term: z.clone().into(),
            guards: vec![Guard {
                relation: fol::Relation::Equal,
                term: GeneralTerm::IntegerTerm(IntegerTerm::BinaryOperation {
                    op: fol::BinaryOperator::Subtract,
                    lhs: IntegerTerm::Variable(i.name.clone()).into(),
                    rhs: k_times_j.clone().into(),
                }),
            }],
        }));

    // Z = I + K * J
    let z_equals_i_plus = Formula::AtomicFormula(fol::AtomicFormula::Comparison(fol::Comparison {
        term: z.into(),
        guards: vec![Guard {
            relation: fol::Relation::Equal,
            term: GeneralTerm::IntegerTerm(IntegerTerm::BinaryOperation {
                op: fol::BinaryOperator::Add,
                lhs: IntegerTerm::Variable(i.name.clone()).into(),
                rhs: k_times_j.into(),
            }),
        }],
    }));

    Formula::BinaryFormula {
        connective: fol::BinaryConnective::Disjunction,
        lhs: Formula::BinaryFormula {
            connective: fol::BinaryConnective::Conjunction,
            lhs: ij_geq_zero.into(),
            rhs: z_equals_i_minus.into(),
        }
        .into(),
        rhs: Formula::BinaryFormula {
            connective: fol::BinaryConnective::Conjunction,
            lhs: ij_less_zero.into(),
            rhs: z_equals_i_plus.into(),
        }
        .into(),
    }
}

// Abstract Gringo compliant integer division and modulo.
// Follows Locally Tight Programs (2023), Conditional literals drafts (2024)
// Division: exists I J K (val_t1(I) & val_t2(J) & F1(IJK) & F2(IJKZ))
// Modulo:   exists I J K (val_t1(I) & val_t2(J) & F1(IJK) & F3(IJKZ))
fn construct_partial_function_formula(
    valti: fol::Formula,
    valtj: fol::Formula,
    binop: asp::BinaryOperator,
    i: fol::Variable,
    j: fol::Variable,
    k: fol::Variable,
    z: fol::Variable,
) -> Formula {
    assert_eq!(i.sort, fol::Sort::Integer);
    assert_eq!(j.sort, fol::Sort::Integer);
    assert_eq!(k.sort, fol::Sort::Integer);
    assert_eq!(z.sort, fol::Sort::General);

    let f1 = division_helper_f1(i.clone(), j.clone(), k.clone());

    let f = match binop {
        asp::BinaryOperator::Divide => division_helper_f2(i.clone(), j.clone(), k.clone(), z),
        asp::BinaryOperator::Modulo => division_helper_f3(i.clone(), j.clone(), k.clone(), z),
        _ => unreachable!("division and modulo are the only supported partial functions"),
    };

    Formula::QuantifiedFormula {
        quantification: Quantification {
            quantifier: Quantifier::Exists,
            variables: vec![i, j, k],
        },
        formula: Formula::conjoin([valti, valtj, f1, f]).into(),
    }
}

// val_t(Z)
pub(crate) fn val(
    t: asp::Term,
    z: fol::Variable,
    taken_variables: IndexSet<fol::Variable>,
) -> Formula {
    let mut taken_variables: IndexSet<fol::Variable> = IndexSet::from_iter(taken_variables);
    taken_variables.insert(z.clone());
    for var in t.variables().iter() {
        taken_variables.insert(fol::Variable {
            name: var.to_string(),
            sort: fol::Sort::General,
        });
    }

    let taken_var_copy = taken_variables.clone();
    let fresh_int_vars = choose_fresh_ijk(&taken_var_copy);

    for (_, value) in fresh_int_vars.iter() {
        taken_variables.insert(value.clone());
    }

    match t {
        asp::Term::PrecomputedTerm(_) | asp::Term::Variable(_) => construct_equality_formula(t, z),
        asp::Term::UnaryOperation { op, arg } => match op {
            asp::UnaryOperator::Negative => {
                let lhs = asp::Term::PrecomputedTerm(asp::PrecomputedTerm::Numeral(0)); // Shorthand for 0 - t
                let valti = val(lhs, fresh_int_vars["I"].clone(), taken_variables.clone()); // val_t1(I)
                let valtj = val(*arg, fresh_int_vars["J"].clone(), taken_variables); // val_t2(J)
                construct_total_function_formula(
                    valti,
                    valtj,
                    asp::BinaryOperator::Subtract,
                    fresh_int_vars["I"].clone(),
                    fresh_int_vars["J"].clone(),
                    z,
                )
            }
            asp::UnaryOperator::AbsoluteValue => {
                let valti = val(*arg, fresh_int_vars["I"].clone(), taken_variables.clone()); // val_t1(I)
                construct_absolute_value_formula(valti, fresh_int_vars["I"].clone(), z)
            }
        },
        asp::Term::BinaryOperation { op, lhs, rhs } => {
            let valti = val(*lhs, fresh_int_vars["I"].clone(), taken_variables.clone()); // val_t1(I)
            let valtj = val(*rhs, fresh_int_vars["J"].clone(), taken_variables); // val_t2(J)
            match op {
                asp::BinaryOperator::Add
                | asp::BinaryOperator::Subtract
                | asp::BinaryOperator::Multiply => construct_total_function_formula(
                    valti,
                    valtj,
                    op,
                    fresh_int_vars["I"].clone(),
                    fresh_int_vars["J"].clone(),
                    z,
                ),
                asp::BinaryOperator::Divide | asp::BinaryOperator::Modulo => {
                    construct_partial_function_formula(
                        valti,
                        valtj,
                        op,
                        fresh_int_vars["I"].clone(),
                        fresh_int_vars["J"].clone(),
                        fresh_int_vars["K"].clone(),
                        z,
                    )
                }
                asp::BinaryOperator::Interval => construct_interval_formula(
                    valti,
                    valtj,
                    fresh_int_vars["I"].clone(),
                    fresh_int_vars["J"].clone(),
                    fresh_int_vars["K"].clone(),
                    z,
                ),
            }
        }
    }
}

// val_t1(Z1) & val_t2(Z2) & ... & val_tn(Zn)
pub(crate) fn valtz(mut terms: Vec<asp::Term>, mut variables: Vec<fol::Variable>) -> fol::Formula {
    fol::Formula::conjoin(
        terms
            .drain(..)
            .zip(variables.drain(..))
            .map(|(t, z)| val(t, z, IndexSet::new())),
    )
}

// Handles the case when we have a rule with a first-order atom or choice atom in the head
fn tau_star_fo_head_rule(r: Rule, globals: &[String]) -> fol::Formula {
    let fol_head_predicate = fol::Predicate::from(r.head.predicate().unwrap());
    let fvars = &globals[0..r.head.arity()]; // V, |V| = n
    let head_terms = r.head.terms().unwrap(); // Transform p(t) into p(V)

    let mut new_terms = Vec::<fol::GeneralTerm>::new();
    let mut fo_vars = Vec::<fol::Variable>::new();
    for (i, _) in head_terms.iter().enumerate() {
        let fol_var = fol::Variable {
            name: fvars[i].to_string(),
            sort: fol::Sort::General,
        };
        let fol_term = fol::GeneralTerm::Variable(fvars[i].to_string());
        fo_vars.push(fol_var);
        new_terms.push(fol_term);
    }

    let valtz = valtz(head_terms.to_vec(), fo_vars); // val_t(V)

    let new_head = fol::Formula::AtomicFormula(fol::AtomicFormula::Atom(fol::Atom {
        predicate_symbol: fol_head_predicate.symbol,
        terms: new_terms,
    })); // p(V)
    let core_lhs = fol::Formula::BinaryFormula {
        connective: fol::BinaryConnective::Conjunction,
        lhs: valtz.into(),
        rhs: tau_body(r.body.clone()).into(),
    };

    let new_body = match r.head {
        asp::mini_gringo::Head::Basic(_) => core_lhs, // val_t(V) & tau^B(Body)
        asp::mini_gringo::Head::Choice(_) => fol::Formula::BinaryFormula {
            // val_t(V) & tau^B(Body) & ~~p(V)
            connective: fol::BinaryConnective::Conjunction,
            lhs: core_lhs.into(),
            rhs: fol::Formula::UnaryFormula {
                connective: fol::UnaryConnective::Negation,
                formula: fol::Formula::UnaryFormula {
                    connective: fol::UnaryConnective::Negation,
                    formula: new_head.clone().into(),
                }
                .into(),
            }
            .into(),
        },
        _ => unreachable!("only atoms and choice rules are supported in this function constructor"),
    };

    fol::Formula::BinaryFormula {
        connective: fol::BinaryConnective::Implication,
        lhs: new_body.into(),
        rhs: new_head.into(),
    }
    .universal_closure()
    // forall G V ( val_t(V) & tau^B(Body) -> p(V) ) OR forall G V ( val_t(V) & tau^B(Body) -> p(V) )
}

// Handles the case when we have a rule with a propositional atom or choice atom in the head
fn tau_star_prop_head_rule(r: &Rule) -> fol::Formula {
    let fol_head_predicate = fol::Predicate::from(r.head.predicate().unwrap());
    let new_head = fol::Formula::AtomicFormula(fol::AtomicFormula::Atom(fol::Atom {
        predicate_symbol: fol_head_predicate.symbol,
        terms: vec![],
    }));
    let core_lhs = tau_body(r.body.clone());
    let new_body = match &r.head {
        asp::mini_gringo::Head::Basic(_) => {
            // tau^B(Body)
            core_lhs
        }
        asp::mini_gringo::Head::Choice(_) => {
            // tau^B(Body) & ~~p
            fol::Formula::BinaryFormula {
                connective: fol::BinaryConnective::Conjunction,
                lhs: core_lhs.into(),
                rhs: fol::Formula::UnaryFormula {
                    connective: fol::UnaryConnective::Negation,
                    formula: fol::Formula::UnaryFormula {
                        connective: fol::UnaryConnective::Negation,
                        formula: new_head.clone().into(),
                    }
                    .into(),
                }
                .into(),
            }
        }
        asp::mini_gringo::Head::Falsity => {
            unreachable!("a constraint head is not permitted in this formula constructor")
        }
    };

    fol::Formula::BinaryFormula {
        // tau^B(Body) -> p OR tau^B(Body) & ~~p -> p
        connective: fol::BinaryConnective::Implication,
        lhs: new_body.into(),
        rhs: new_head.into(),
    }
    .universal_closure()
    // forall G ( tau^B(Body) -> p ) OR forall G ( tau^B(Body) & ~~p -> p )
}

// Translate a rule using a pre-defined list of global variables
fn tau_star_rule(r: &Rule, globals: &[String]) -> fol::Formula {
    match r.head.predicate() {
        Some(_) => {
            if r.head.arity() > 0 {
                // First-order head
                tau_star_fo_head_rule(r.clone(), globals)
            } else {
                // Propositional head
                tau_star_prop_head_rule(r)
            }
        }
        // Handles the case when we have a rule with an empty head
        None => fol::Formula::BinaryFormula {
            connective: fol::BinaryConnective::Implication,
            lhs: tau_body(r.body.clone()).into(),
            rhs: fol::Formula::AtomicFormula(fol::AtomicFormula::Falsity).into(),
        }
        .universal_closure(),
    }
}

// For each rule, produce a formula: forall G V ( val_t(V) & tau_body(Body) -> p(V) )
// Where G is all variables from the original rule
// and V is the set of fresh variables replacing t within p
pub fn tau_star(p: Program) -> fol::Theory {
    let globals = choose_fresh_global_variables(&p);
    let mut formulas: Vec<fol::Formula> = vec![]; // { forall G V ( val_t(V) & tau^B(Body) -> p(V) ), ... }
    for r in p.rules.iter() {
        formulas.push(tau_star_rule(r, &globals));
    }
    fol::Theory { formulas }
}

#[cfg(test)]
mod tests {

    use super::valtz;

    #[test]
    fn test_valtz() {
        for (term, var, target) in [
            (
                "X + 1",
                "Z1",
                "exists I$i J$i (Z1$g = I$i + J$i and I$i = X and J$i = 1)",
            ),
            (
                "3 - 5",
                "Z1",
                "exists I$i J$i (Z1$g = I$i - J$i and I$i = 3 and J$i = 5)",
            ),
            (
                "1 / 0",
                "Z",
                "exists I$i J$i K$i (I$i = 1 and J$i = 0 and (K$i * |J$i| <= |I$i| < (K$i + 1) * |J$i|) and ((I$i * J$i >= 0 and Z = K$i) or (I$i * J$i < 0 and Z = -K$i)))",
            ),
            (
                "1 \\ 0",
                "Z",
                "exists I$i J$i K$i (I$i = 1 and J$i = 0 and (K$i * |J$i| <= |I$i| < (K$i + 1) * |J$i|) and ((I$i * J$i >= 0 and Z = (I$i - K$i * J$i)) or (I$i * J$i < 0 and Z = (I$i + K$i * J$i))))",
            ),
            (
                "X..Y",
                "Z",
                "exists I$i J$i K$i (I$i = X and J$i = Y and Z$g = K$i and I$i <= K$i <= J$i)",
            ),
            (
                "X+1..Y",
                "Z1",
                "exists I$i J$i K$i ((exists I1$i J1$i (I$i = I1$i + J1$i and I1$i = X and J1$i = 1)) and J$i = Y and Z1 = K$i and I$i <= K$i <= J$i)",
            ),
        ] {
            let left = valtz(vec![term.parse().unwrap()], vec![var.parse().unwrap()]);
            let right = target.parse().unwrap();

            assert!(
                left == right,
                "assertion `left == right` failed:\n left:\n{left}\n right:\n{right}"
            );
        }
    }
}
