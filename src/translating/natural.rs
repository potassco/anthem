//! Natural translation
//! [1] Transforming Gringo Rules into Formulas in a Natural Way; Lifschitz V. 2021
//! [2] Here and There with Arithmetics; Lifschitz V. 2021
//! [3]
//! [4]
//! It follows the description given in [1]
//! The other papers give examples of the translation which were used in the tests

use {
    crate::syntax_tree::{asp, fol},
    crate::translating::tau_star,
    indexmap::IndexSet,
};

fn contains_symbol_or_infimum_or_supremum(t: &asp::Term) -> bool {
    match t {
        asp::Term::Variable(_) => false,
        asp::Term::PrecomputedTerm(asp::PrecomputedTerm::Symbol(_)) => true,
        asp::Term::PrecomputedTerm(asp::PrecomputedTerm::Infimum) => true,
        asp::Term::PrecomputedTerm(asp::PrecomputedTerm::Supremum) => true,
        asp::Term::PrecomputedTerm(asp::PrecomputedTerm::Numeral(_)) => false,
        asp::Term::UnaryOperation {
            op: asp::UnaryOperator::Negative,
            arg,
        } => contains_symbol_or_infimum_or_supremum(&arg),
        asp::Term::BinaryOperation { lhs, rhs, .. } => {
            contains_symbol_or_infimum_or_supremum(&lhs)
                || contains_symbol_or_infimum_or_supremum(&rhs)
        }
    }
}

fn is_term_regular_of_first_kind(t: &asp::Term) -> bool {
    match t {
        asp::Term::Variable(_) => true,
        asp::Term::PrecomputedTerm(_) => true,
        asp::Term::UnaryOperation {
            op: asp::UnaryOperator::Negative,
            arg,
        } => is_term_regular_of_first_kind(&arg) && !contains_symbol_or_infimum_or_supremum(&arg),
        asp::Term::BinaryOperation {
            op:
                asp::BinaryOperator::Add | asp::BinaryOperator::Subtract | asp::BinaryOperator::Multiply,
            lhs,
            rhs,
        } => {
            is_term_regular_of_first_kind(&lhs)
                && !contains_symbol_or_infimum_or_supremum(&lhs)
                && is_term_regular_of_first_kind(&rhs)
                && !contains_symbol_or_infimum_or_supremum(&rhs)
        }
        _ => false,
    }
}

fn is_term_regular_of_second_kind(t: &asp::Term) -> bool {
    match t {
        asp::Term::BinaryOperation {
            op: asp::BinaryOperator::Interval,
            lhs,
            rhs,
        } => {
            is_term_regular_of_first_kind(&lhs)
                && !contains_symbol_or_infimum_or_supremum(&lhs)
                && is_term_regular_of_first_kind(&rhs)
                && !contains_symbol_or_infimum_or_supremum(&rhs)
        }
        _ => false,
    }
}

fn p2f(t: &asp::Term, int_vars: &IndexSet<std::string::String>) -> Option<fol::GeneralTerm> {
    // translates a term of first kind
    // check that t is regular of first kind and return None if not
    if !is_term_regular_of_first_kind(&t) {
        return None;
    }

    match t {
        asp::Term::Variable(v) => {
            if int_vars.contains(v.0.as_str()) {
                Some(fol::GeneralTerm::IntegerTerm(fol::IntegerTerm::Variable(
                    v.0.clone(), // TODO: choose fresh variable names?
                )))
            } else {
                Some(fol::GeneralTerm::Variable(v.0.clone()))
            }
        }
        asp::Term::PrecomputedTerm(p) => match p {
            asp::PrecomputedTerm::Infimum => Some(fol::GeneralTerm::Infimum),
            asp::PrecomputedTerm::Numeral(i) => {
                Some(fol::GeneralTerm::IntegerTerm(fol::IntegerTerm::Numeral(*i)))
            }
            asp::PrecomputedTerm::Symbol(s) => Some(fol::GeneralTerm::SymbolicTerm(
                fol::SymbolicTerm::Symbol(s.to_string()),
            )),
            asp::PrecomputedTerm::Supremum => Some(fol::GeneralTerm::Supremum),
        },
        _ => p2f_int_term(t).map(fol::GeneralTerm::IntegerTerm),
    }
}

fn p2f_int_term(t: &asp::Term) -> Option<fol::IntegerTerm> {
    // translates a (integer) term of first kind
    // TODO: choose fresh variable names?
    match t {
        asp::Term::Variable(v) => Some(fol::IntegerTerm::Variable(v.0.clone())),
        asp::Term::PrecomputedTerm(asp::PrecomputedTerm::Numeral(i)) => {
            Some(fol::IntegerTerm::Numeral(*i))
        }
        asp::Term::UnaryOperation {
            op: asp::UnaryOperator::Negative,
            arg,
        } => Some(fol::IntegerTerm::UnaryOperation {
            op: fol::UnaryOperator::Negative,
            arg: Box::new(p2f_int_term(arg)?),
        }),
        asp::Term::BinaryOperation { op, lhs, rhs } => {
            let op = match op {
                asp::BinaryOperator::Add => fol::BinaryOperator::Add,
                asp::BinaryOperator::Subtract => fol::BinaryOperator::Subtract,
                asp::BinaryOperator::Multiply => fol::BinaryOperator::Multiply,
                _ => return None,
            };
            Some(fol::IntegerTerm::BinaryOperation {
                op,
                lhs: Box::new(p2f_int_term(lhs)?),
                rhs: Box::new(p2f_int_term(rhs)?),
            })
        }
        _ => None,
    }
}

fn get_int_variables(r: &asp::Rule) -> IndexSet<std::string::String> {
    // Parse rule and return all variables appearing at least once in the scope of unary/binary operations/comparison
    let mut vars = IndexSet::<std::string::String>::new();
    // iterate over all terms in the rule and then over all variables in the term
    for term in r.terms() {
        match term {
            asp::Term::UnaryOperation { op: _, arg } => {
                // add all variables from arg to vars
                vars.extend(arg.variables().into_iter().map(|v| v.0));
            }
            asp::Term::BinaryOperation { lhs, rhs, .. } => {
                // add all variables from lhs and rhs to vars
                vars.extend(lhs.variables().into_iter().map(|v| v.0));
                vars.extend(rhs.variables().into_iter().map(|v| v.0));
            }
            _ => (),
        }
    }
    // iterate over all comparisons in the body
    for f in r.body.formulas.iter() {
        if let asp::AtomicFormula::Comparison(c) = f {
            if c.relation == asp::Relation::Equal && is_term_regular_of_second_kind(&c.rhs) {
                vars.extend(c.lhs.variables().into_iter().map(|v| v.0));
            }
        }
    }

    vars
}

fn natural_comparison(
    c: &asp::Comparison,
    int_vars: &IndexSet<std::string::String>,
) -> Option<fol::Formula> {
    // translate comparison

    let f_relation = match c.relation {
        asp::Relation::Equal => fol::Relation::Equal,
        asp::Relation::NotEqual => fol::Relation::NotEqual,
        asp::Relation::Greater => fol::Relation::Greater,
        asp::Relation::Less => fol::Relation::Less,
        asp::Relation::GreaterEqual => fol::Relation::GreaterEqual,
        asp::Relation::LessEqual => fol::Relation::LessEqual,
    };
    // TODO: would be nice to have: let f_relation: fol::Relation = c.relation.into();

    let lhs = p2f(&c.lhs, &int_vars)?;
    let comp_formula =
        if f_relation == fol::Relation::Equal && is_term_regular_of_second_kind(&c.rhs) {
            if let asp::Term::BinaryOperation {
                lhs: t2, rhs: t3, ..
            } = &c.rhs
            {
                let t2 = p2f(&t2, &int_vars)?;
                let t3 = p2f(&t3, &int_vars)?;
                fol::Formula::AtomicFormula(fol::AtomicFormula::Comparison(fol::Comparison {
                    term: t2,
                    guards: vec![
                        fol::Guard {
                            relation: fol::Relation::LessEqual,
                            term: lhs.clone(),
                        },
                        fol::Guard {
                            relation: fol::Relation::LessEqual,
                            term: t3,
                        },
                    ],
                }))
            } else {
                return None;
            }
        } else {
            let rhs = p2f(&c.rhs, &int_vars)?;
            fol::Formula::AtomicFormula(fol::AtomicFormula::Comparison(fol::Comparison {
                term: lhs,
                guards: vec![fol::Guard {
                    relation: f_relation,
                    term: rhs,
                }],
            }))
        };
    Some(comp_formula)
}

fn natural_b_atom(l: &asp::Atom, int_vars: &IndexSet<std::string::String>) -> Option<fol::Atom> {
    let mut terms = Vec::<fol::GeneralTerm>::new();
    for t in &l.terms {
        terms.push(p2f(t, &int_vars)?);
    }
    Some(fol::Atom {
        predicate_symbol: l.predicate_symbol.to_string(),
        terms,
    })
}

fn natural_b_literal(
    l: &asp::Literal,
    int_vars: &IndexSet<std::string::String>,
) -> Option<fol::Formula> {
    let atom = natural_b_atom(&l.atom, &int_vars)?;
    Some(match l.sign {
        asp::Sign::NoSign => fol::Formula::AtomicFormula(fol::AtomicFormula::Atom(atom)),
        asp::Sign::Negation => fol::Formula::UnaryFormula {
            connective: fol::UnaryConnective::Negation,
            formula: Box::new(fol::Formula::AtomicFormula(fol::AtomicFormula::Atom(atom))),
        },
        asp::Sign::DoubleNegation => fol::Formula::UnaryFormula {
            connective: fol::UnaryConnective::Negation,
            formula: Box::new(fol::Formula::UnaryFormula {
                connective: fol::UnaryConnective::Negation,
                formula: Box::new(fol::Formula::AtomicFormula(fol::AtomicFormula::Atom(atom))),
            }),
        },
    })
}

fn natural_body(b: &asp::Body, int_vars: &IndexSet<std::string::String>) -> Option<fol::Formula> {
    let mut formulas = Vec::<fol::Formula>::new();
    for f in b.formulas.iter() {
        match f {
            asp::AtomicFormula::Literal(l) => {
                formulas.push(natural_b_literal(&l, &int_vars)?);
            }
            asp::AtomicFormula::Comparison(c) => {
                formulas.push(natural_comparison(&c, &int_vars)?);
            }
        }
    }
    Some(fol::Formula::conjoin(formulas))
}

fn get_fresh_variables_for_head_atom(a: &asp::Atom) -> Vec<String> {
    let mut fresh_vars = Vec::<String>::new();
    let taken_vars = a.variables();
    let terms = &a.terms;
    for (i, term) in terms.iter().enumerate() {
        if !is_term_regular_of_first_kind(term) {
            // create a new variable with N_i if not of first kind
            let var_name = format!("N{}", i);
            // check if var_name is already taken
            if !taken_vars.contains(&asp::Variable(var_name.clone())) {
                // add var_name to fresh_vars
                fresh_vars.push(var_name);
            } else {
                // var is taken already
                // add a new variable with name N_i_j to fresh_vars
                let mut j = 0;
                loop {
                    let var_name = format!("N{}_{}", i, j);
                    if !taken_vars.contains(&asp::Variable(var_name.clone())) {
                        fresh_vars.push(var_name);
                        break;
                    }
                    j += 1;
                }
            }
        }
    }

    fresh_vars
}

fn natural_head_atom(
    a: &asp::Atom,
    int_vars: &IndexSet<std::string::String>,
    fresh_vars: &Vec<String>,
) -> Option<fol::Formula> {
    // If head is not regular, returns None
    // If head is regular returns the atom with intervals replaced by fresh variables and regular terms translated:
    // Example: p(a, 1..10, X, I+1) -> p(a, N1$i, X, I$i + 1)
    let mut terms = Vec::<fol::GeneralTerm>::new();
    // create an iterator over fresh_vars
    let mut fresh_vars = fresh_vars.iter();
    for t in &a.terms {
        if is_term_regular_of_first_kind(&t) {
            terms.push(p2f(&t, &int_vars)?);
        } else if is_term_regular_of_second_kind(&t) {
            let fresh_var = fresh_vars.next().unwrap();
            terms.push(fol::GeneralTerm::IntegerTerm(fol::IntegerTerm::Variable(
                fresh_var.clone(),
            )));
        } else {
            return None;
        };
    }
    Some(fol::Formula::AtomicFormula(fol::AtomicFormula::Atom(
        fol::Atom {
            predicate_symbol: a.predicate_symbol.clone(),
            terms,
        },
    )))
}

fn natural_head_interval(
    a: &asp::Atom,
    int_vars: &IndexSet<std::string::String>,
    fresh_vars: &Vec<String>,
) -> Option<fol::Formula> {
    let mut formulas = Vec::<fol::Formula>::new();
    let mut fresh_vars = fresh_vars.iter();
    for t in &a.terms {
        if is_term_regular_of_second_kind(&t) {
            // term is of form t1..t2 with t1, t2 regular of first kind, or not natural rule
            let t1 = match t {
                asp::Term::BinaryOperation { lhs, .. } => lhs,
                _ => unreachable!("term is not a binary operation."),
            };
            let t2 = match t {
                asp::Term::BinaryOperation { rhs, .. } => rhs,
                _ => unreachable!("term is not a binary operation."),
            };
            let fresh_var = fresh_vars.next().unwrap();
            // create formula for t1 <= fresh_var and fresh_var <= t2
            let comp_formula =
                fol::Formula::AtomicFormula(fol::AtomicFormula::Comparison(fol::Comparison {
                    term: p2f(&t1, &int_vars)?,
                    guards: vec![
                        fol::Guard {
                            relation: fol::Relation::LessEqual,
                            term: fol::GeneralTerm::IntegerTerm(fol::IntegerTerm::Variable(
                                fresh_var.clone(),
                            )),
                        },
                        fol::Guard {
                            relation: fol::Relation::LessEqual,
                            term: p2f(&t2, &int_vars)?,
                        },
                    ],
                }));

            // add comp_formula to formulas
            formulas.push(comp_formula);
        }
    }
    // conjoin all formulas
    Some(fol::Formula::conjoin(formulas))
}

fn natural_basic_head(
    a: &asp::Atom,
    int_vars: &IndexSet<std::string::String>,
) -> Option<fol::Formula> {
    let fresh_vars = get_fresh_variables_for_head_atom(&a);
    let conclusion = natural_head_atom(a, int_vars, &fresh_vars)?;
    if fresh_vars.is_empty() {
        return Some(conclusion);
    }
    let quantification = fol::Quantification {
        quantifier: fol::Quantifier::Forall,
        variables: fresh_vars
            .iter()
            .map(|v| fol::Variable {
                sort: fol::Sort::Integer,
                name: v.clone(),
            })
            .collect(),
    };
    let conditions = natural_head_interval(&a, int_vars, &fresh_vars)?;
    Some(fol::Formula::QuantifiedFormula {
        quantification,
        formula: Box::new(fol::Formula::BinaryFormula {
            connective: fol::BinaryConnective::Implication,
            lhs: conditions.into(),
            rhs: conclusion.into(),
        }),
    })
}

fn natural_choice_head(
    a: &asp::Atom,
    int_vars: &IndexSet<std::string::String>,
) -> Option<fol::Formula> {
    let fresh_vars = get_fresh_variables_for_head_atom(&a);
    let head_atom = natural_head_atom(a, int_vars, &fresh_vars)?;
    // conclusion is a disjunction of natural_head_atom and its negation
    let conclusion = fol::Formula::BinaryFormula {
        connective: fol::BinaryConnective::Disjunction,
        lhs: head_atom.clone().into(),
        rhs: fol::Formula::UnaryFormula {
            connective: fol::UnaryConnective::Negation,
            formula: Box::new(head_atom.clone().into()),
        }
        .into(),
    };
    if fresh_vars.is_empty() {
        return Some(conclusion);
    }
    let quantification = fol::Quantification {
        quantifier: fol::Quantifier::Forall,
        variables: fresh_vars
            .iter()
            .map(|v| fol::Variable {
                sort: fol::Sort::Integer,
                name: v.clone(),
            })
            .collect(),
    };
    let conditions = natural_head_interval(&a, int_vars, &fresh_vars)?;
    Some(fol::Formula::QuantifiedFormula {
        quantification,
        formula: Box::new(fol::Formula::BinaryFormula {
            connective: fol::BinaryConnective::Implication,
            lhs: conditions.into(),
            rhs: conclusion.into(),
        }),
    })
}

fn natural_constraint() -> fol::Formula {
    fol::Formula::AtomicFormula(fol::AtomicFormula::Falsity)
}

fn natural_head(h: &asp::Head, int_vars: &IndexSet<std::string::String>) -> Option<fol::Formula> {
    match h {
        asp::Head::Basic(a) => natural_basic_head(&a, int_vars),
        asp::Head::Choice(a) => natural_choice_head(&a, int_vars),
        asp::Head::Falsity => Some(natural_constraint()),
    }
}

fn natural_rule(r: &asp::Rule) -> Option<fol::Formula> {
    let int_vars = get_int_variables(r);
    let head = natural_head(&r.head, &int_vars)?;
    let body = natural_body(&r.body, &int_vars)?;
    Some(
        (fol::Formula::BinaryFormula {
            connective: fol::BinaryConnective::Implication,
            lhs: body.into(),
            rhs: head.into(),
        })
        .universal_closure(),
    )
}

pub fn mu(p: asp::Program) -> fol::Theory {
    // should this be mu?
    let mut formulas: Vec<fol::Formula> = vec![];
    let globals = tau_star::choose_fresh_global_variables(&p);
    for r in p.rules.iter() {
        let fol_rule = natural_rule(r);
        match fol_rule {
            Some(f) => formulas.push(f),
            None => formulas.push(tau_star::tau_star_rule(r, &globals)),
        }
    }
    fol::Theory { formulas }
}

#[cfg(test)]
mod tests {
    use indexmap::IndexSet;

    use super::{
        contains_symbol_or_infimum_or_supremum, fol, get_int_variables,
        is_term_regular_of_first_kind, is_term_regular_of_second_kind, natural_comparison,
        natural_rule, p2f, p2f_int_term,
    };

    #[test]
    fn test_contains_symbol_or_infimum_or_supremum() {
        for (source, target) in [
            ("3", false),
            ("a", true),
            ("inf", true),
            ("sup", true),
            ("-3", false),
            ("3+5", false),
            ("3-5", false),
            ("3*5", false),
            ("3/5", false),
            ("3..5", false),
            ("X", false),
            ("X..Y", false),
        ] {
            let contains = contains_symbol_or_infimum_or_supremum(&source.parse().unwrap());

            assert!(
                contains == target,
                "assertion `contains_symbol_or_infimum_or_supremum{source} == target` failed:\n contains:\n{contains}\n target:\n{target}"
            );
        }
    }

    #[test]
    fn test_is_term_regular_of_first_kind() {
        for (source, target) in [
            ("X", true),
            ("a", true),
            ("inf", true),
            ("sup", true),
            ("-3", true),
            ("3+5", true),
            ("3-5", true),
            ("X*5", true),
            ("3/5", false),
            ("3..5", false),
            ("X..Y", false),
            ("3+5*2", true),
            ("3+5/2", false),
            ("3+2..5", false),
            ("3+5*2..3", false),
            ("(3+5)*(1-2)", true),
            ("(a)*(1-2)", false),
            ("(a)", true),
            ("(a+2)*(1-2)", false),
        ] {
            let is_regular = is_term_regular_of_first_kind(&source.parse().unwrap());

            assert!(
                is_regular == target,
                "assertion `is_term_regular_of_first_kind({source}) == target` failed:\n is_regular:\n{is_regular}\n target:\n{target}"
            );
        }
    }

    #[test]
    fn test_is_term_regular_of_second_kind() {
        for (source, target) in [
            ("3", false),
            ("a", false),
            ("inf", false),
            ("sup", false),
            ("-3", false),
            ("3+5", false),
            ("3-5", false),
            ("X*5", false),
            ("3/5", false),
            ("3..5", true),
            ("X..Y", true),
            ("(3+5*2)..Y", true),
            ("3+5/2", false),
            ("inf..5", false),
            ("3+5*2..3", true),
            ("4+(5..6)", false),
            ("(3+5)..(1-2)", true),
            ("(a)..(1-2)", false),
        ] {
            let is_regular = is_term_regular_of_second_kind(&source.parse().unwrap());

            assert!(
                is_regular == target,
                "assertion `is_term_regular_of_second_kind({source}) == target` failed:\n is_regular:\n{is_regular}\n target:\n{target}"
            );
        }
    }

    #[test]
    fn test_p2f() {
        for (source, target, int_vars) in [
            (
                "3",
                Some(fol::GeneralTerm::IntegerTerm(fol::IntegerTerm::Numeral(3))),
                IndexSet::new(),
            ),
            (
                "--3",
                Some(fol::GeneralTerm::IntegerTerm(
                    fol::IntegerTerm::UnaryOperation {
                        op: fol::UnaryOperator::Negative,
                        arg: Box::new(fol::IntegerTerm::Numeral(-3)),
                    },
                )),
                IndexSet::new(),
            ),
            (
                "3+5",
                Some(fol::GeneralTerm::IntegerTerm(
                    fol::IntegerTerm::BinaryOperation {
                        op: fol::BinaryOperator::Add,
                        lhs: Box::new(fol::IntegerTerm::Numeral(3)),
                        rhs: Box::new(fol::IntegerTerm::Numeral(5)),
                    },
                )),
                IndexSet::new(),
            ),
            (
                "3-5",
                Some(fol::GeneralTerm::IntegerTerm(
                    fol::IntegerTerm::BinaryOperation {
                        op: fol::BinaryOperator::Subtract,
                        lhs: Box::new(fol::IntegerTerm::Numeral(3)),
                        rhs: Box::new(fol::IntegerTerm::Numeral(5)),
                    },
                )),
                IndexSet::new(),
            ),
            (
                "a",
                Some(fol::GeneralTerm::SymbolicTerm(fol::SymbolicTerm::Symbol(
                    "a".to_string(),
                ))),
                IndexSet::new(),
            ),
            ("#inf", Some(fol::GeneralTerm::Infimum), IndexSet::new()),
            ("#sup", Some(fol::GeneralTerm::Supremum), IndexSet::new()),
            (
                "X",
                Some(fol::GeneralTerm::Variable("X".to_string())),
                IndexSet::new(),
            ),
            (
                "X",
                Some(fol::GeneralTerm::IntegerTerm(fol::IntegerTerm::Variable(
                    "X".to_string(),
                ))),
                {
                    let mut set = IndexSet::new();
                    set.insert("X".to_string());
                    set
                },
            ),
            (
                "X*5",
                Some(fol::GeneralTerm::IntegerTerm(
                    fol::IntegerTerm::BinaryOperation {
                        op: fol::BinaryOperator::Multiply,
                        lhs: Box::new(fol::IntegerTerm::Variable("X".to_string())),
                        rhs: Box::new(fol::IntegerTerm::Numeral(5)),
                    },
                )),
                {
                    let mut set = IndexSet::new();
                    set.insert("X".to_string());
                    set
                },
            ),
            ("3/5", None, IndexSet::new()),
            ("3..5", None, IndexSet::new()),
            ("X..Y", None, {
                let mut set = IndexSet::new();
                set.insert("X".to_string());
                set.insert("Y".to_string());
                set
            }),
        ] {
            let p2f_term = p2f(&source.parse().unwrap(), &int_vars);

            assert_eq!(
                p2f_term, target,
                "assertion `p2f({source}) == target` failed:\n p2f_term:\n{p2f_term:?}\n target:\n{target:?}\n int_vars: {int_vars:?}"
            );
        }
    }

    #[test]
    fn test_p2f_int_term() {
        for (source, target) in [
            ("3", Some(fol::IntegerTerm::Numeral(3))),
            ("-3", Some(fol::IntegerTerm::Numeral(-3))),
            (
                "--3",
                Some(fol::IntegerTerm::UnaryOperation {
                    op: fol::UnaryOperator::Negative,
                    arg: Box::new(fol::IntegerTerm::Numeral(-3)),
                }),
            ),
            (
                "3+5",
                Some(fol::IntegerTerm::BinaryOperation {
                    op: fol::BinaryOperator::Add,
                    lhs: Box::new(fol::IntegerTerm::Numeral(3)),
                    rhs: Box::new(fol::IntegerTerm::Numeral(5)),
                }),
            ),
            (
                "3-5",
                Some(fol::IntegerTerm::BinaryOperation {
                    op: fol::BinaryOperator::Subtract,
                    lhs: Box::new(fol::IntegerTerm::Numeral(3)),
                    rhs: Box::new(fol::IntegerTerm::Numeral(5)),
                }),
            ),
            (
                "3*5",
                Some(fol::IntegerTerm::BinaryOperation {
                    op: fol::BinaryOperator::Multiply,
                    lhs: Box::new(fol::IntegerTerm::Numeral(3)),
                    rhs: Box::new(fol::IntegerTerm::Numeral(5)),
                }),
            ),
            ("X", Some(fol::IntegerTerm::Variable("X".to_string()))),
            (
                "-X",
                Some(fol::IntegerTerm::UnaryOperation {
                    op: fol::UnaryOperator::Negative,
                    arg: Box::new(fol::IntegerTerm::Variable("X".to_string())),
                }),
            ),
            (
                "X+5",
                Some(fol::IntegerTerm::BinaryOperation {
                    op: fol::BinaryOperator::Add,
                    lhs: Box::new(fol::IntegerTerm::Variable("X".to_string())),
                    rhs: Box::new(fol::IntegerTerm::Numeral(5)),
                }),
            ),
            (
                "X-5",
                Some(fol::IntegerTerm::BinaryOperation {
                    op: fol::BinaryOperator::Subtract,
                    lhs: Box::new(fol::IntegerTerm::Variable("X".to_string())),
                    rhs: Box::new(fol::IntegerTerm::Numeral(5)),
                }),
            ),
            (
                "X*5",
                Some(fol::IntegerTerm::BinaryOperation {
                    op: fol::BinaryOperator::Multiply,
                    lhs: Box::new(fol::IntegerTerm::Variable("X".to_string())),
                    rhs: Box::new(fol::IntegerTerm::Numeral(5)),
                }),
            ),
            (
                "X*Y",
                Some(fol::IntegerTerm::BinaryOperation {
                    op: fol::BinaryOperator::Multiply,
                    lhs: Box::new(fol::IntegerTerm::Variable("X".to_string())),
                    rhs: Box::new(fol::IntegerTerm::Variable("Y".to_string())),
                }),
            ),
            ("2..5", None),
            ("X..Y", None),
            ("a", None),
            ("inf", None),
            ("sup", None),
        ] {
            let p2f_int = p2f_int_term(&source.parse().unwrap());

            let p2f_int_clone = p2f_int.clone();
            assert_eq!(
            p2f_int_clone, target,
            "assertion `p2f_int_term({source}) == target` failed:\n p2f_int:\n{p2f_int:?}\n target:\n{target:?}"
            );
        }
    }

    #[test]
    fn test_get_int_variables() {
        for (rule, expected) in [
            ("p(X).", vec![]),
            ("p(X +2).", vec!["X"]),
            ("p(X+2) :- X = Y + 2, q(Y).", vec!["X", "Y"]),
            ("p(X) :- X = 3.", vec![]),
            ("p(X) :- X = 3..5.", vec!["X"]),
            ("q(x) :- p(X), X = 3..5, Y = 4.", vec!["X"]),
            ("p(X) :- X = 3..5, Y < 4, Z = 5..6.", vec!["X", "Z"]),
            ("p(X) :- X = 3..5, Y = 4, Z = 5..6, X = a.", vec!["X", "Z"]),
            ("p(X..Y).", vec!["X", "Y"]),
            ("p(X, a, 4+5..X+Y):- Z = X + Y.", vec!["X", "Y"]),
        ] {
            let rule = rule.parse().unwrap();
            let int_vars = get_int_variables(&rule);
            let mut expected_set = IndexSet::new();
            for var in expected {
                expected_set.insert(var.to_string());
            }
            assert_eq!(int_vars, expected_set,
            "assertion `get_int_variables({rule}) == expected` failed:\n int_vars:\n{int_vars:?}\n expected_set:\n{expected_set:?}",
            );
        }
    }

    #[test]
    fn test_natural_comparison() {
        for (source, target, int_vars) in [
            (
                "3 = 3",
                Some(fol::Formula::AtomicFormula(fol::AtomicFormula::Comparison(
                    fol::Comparison {
                        term: fol::GeneralTerm::IntegerTerm(fol::IntegerTerm::Numeral(3)),
                        guards: vec![fol::Guard {
                            relation: fol::Relation::Equal,
                            term: fol::GeneralTerm::IntegerTerm(fol::IntegerTerm::Numeral(3)),
                        }],
                    },
                ))),
                vec![],
            ),
            (
                "X = 3",
                Some(fol::Formula::AtomicFormula(fol::AtomicFormula::Comparison(
                    fol::Comparison {
                        term: fol::GeneralTerm::Variable("X".to_string()),
                        guards: vec![fol::Guard {
                            relation: fol::Relation::Equal,
                            term: fol::GeneralTerm::IntegerTerm(fol::IntegerTerm::Numeral(3)),
                        }],
                    },
                ))),
                vec![],
            ),
            (
                "X < 3",
                Some(fol::Formula::AtomicFormula(fol::AtomicFormula::Comparison(
                    fol::Comparison {
                        term: fol::GeneralTerm::Variable("X".to_string()),
                        guards: vec![fol::Guard {
                            relation: fol::Relation::Less,
                            term: fol::GeneralTerm::IntegerTerm(fol::IntegerTerm::Numeral(3)),
                        }],
                    },
                ))),
                vec![],
            ),
            (
                "X = 3",
                Some(fol::Formula::AtomicFormula(fol::AtomicFormula::Comparison(
                    fol::Comparison {
                        term: fol::GeneralTerm::IntegerTerm(fol::IntegerTerm::Variable(
                            "X".to_string(),
                        )),
                        guards: vec![fol::Guard {
                            relation: fol::Relation::Equal,
                            term: fol::GeneralTerm::IntegerTerm(fol::IntegerTerm::Numeral(3)),
                        }],
                    },
                ))),
                vec!["X".to_string()],
            ),
            (
                "3 = 3..5",
                Some(fol::Formula::AtomicFormula(fol::AtomicFormula::Comparison(
                    fol::Comparison {
                        term: fol::GeneralTerm::IntegerTerm(fol::IntegerTerm::Numeral(3)),
                        guards: vec![
                            fol::Guard {
                                relation: fol::Relation::LessEqual,
                                term: fol::GeneralTerm::IntegerTerm(fol::IntegerTerm::Numeral(3)),
                            },
                            fol::Guard {
                                relation: fol::Relation::LessEqual,
                                term: fol::GeneralTerm::IntegerTerm(fol::IntegerTerm::Numeral(5)),
                            },
                        ],
                    },
                ))),
                vec![],
            ),
            (
                "X = 3..5",
                Some(fol::Formula::AtomicFormula(fol::AtomicFormula::Comparison(
                    fol::Comparison {
                        term: fol::GeneralTerm::IntegerTerm(fol::IntegerTerm::Numeral(3)),
                        guards: vec![
                            fol::Guard {
                                relation: fol::Relation::LessEqual,
                                term: fol::GeneralTerm::IntegerTerm(fol::IntegerTerm::Variable(
                                    "X".to_string(),
                                )),
                            },
                            fol::Guard {
                                relation: fol::Relation::LessEqual,
                                term: fol::GeneralTerm::IntegerTerm(fol::IntegerTerm::Numeral(5)),
                            },
                        ],
                    },
                ))),
                vec!["X".to_string()],
            ),
            (
                "X = Y+5..3",
                Some(fol::Formula::AtomicFormula(fol::AtomicFormula::Comparison(
                    fol::Comparison {
                        term: fol::GeneralTerm::IntegerTerm(fol::IntegerTerm::BinaryOperation {
                            op: fol::BinaryOperator::Add,
                            lhs: Box::new(fol::IntegerTerm::Variable("Y".to_string())),
                            rhs: Box::new(fol::IntegerTerm::Numeral(5)),
                        }),
                        guards: vec![
                            fol::Guard {
                                relation: fol::Relation::LessEqual,
                                term: fol::GeneralTerm::IntegerTerm(fol::IntegerTerm::Variable(
                                    "X".to_string(),
                                )),
                            },
                            fol::Guard {
                                relation: fol::Relation::LessEqual,
                                term: fol::GeneralTerm::IntegerTerm(fol::IntegerTerm::Numeral(3)),
                            },
                        ],
                    },
                ))),
                vec!["X".to_string(), "Y".to_string()],
            ),
        ] {
            let source = source.parse().unwrap();
            let mut int_set = IndexSet::new();
            for var in int_vars {
                int_set.insert(var.to_string());
            }
            let comp = natural_comparison(&source, &int_set);

            assert_eq!(comp, target,
            "assertion `natural_comparison({source}) == target` failed:\n comp:\n{comp:?}\n target:\n{target:?}\n int_vars: {int_set:?}",
            );
        }
    }

    #[test]
    fn test_natural_rule() {
        for (source, target) in [
            ("p(X) :- X = 3.", "forall X (X = 3 -> p(X))"),
            ("{p(X)} :- X = 3.", "forall X (X = 3 -> p(X) or not p(X))"),
            ("p(1..2, N0).", "forall N0 (#true -> forall N0_0$i (1 <= N0_0$i <= 2-> p(N0_0$i, N0)))"),
            ("q(X+1) :- p(X).", "forall X$i (p(X$i) -> q(X$i + 1))"), // example (1) from paper [1]
            (" :- p(X,Y,Z), X < Y, Y=1..Z.", "forall X Y$i Z$i (p(X, Y$i, Z$i) and X < Y$i and (1 <= Y$i <= Z$i) -> #false)"), // example from paper [1]
            ("q(1..X, 1..Y) :- p(X,Y,Z).",
            "forall X$i Y$i Z (p(X$i, Y$i, Z) -> forall N0$i N1$i (1 <= N0$i <= X$i and (1 <= N1$i <= Y$i) -> q(N0$i, N1$i)))"), //( example from paper [1]
            ("{q(1..X, Y)} :- p(X,Y).", "forall X$i Y (p(X$i, Y) -> forall N0$i (1 <= N0$i <= X$i -> q(N0$i, Y) or not q(N0$i, Y)))"), // example from paper [1]
            ("p(X,Y) :- X = 1..2, Y = 1..2.", "forall X$i Y$i (1 <= X$i <= 2 and (1 <= Y$i <= 2) -> p(X$i, Y$i))"), // example (6) from paper [2]
            ("p(X,Y) :- X = Y, Y = 1..2.", "forall X Y$i ( X = Y$i and (1 <= Y$i  <= 2) -> p(X, Y$i))" ), // example (7) from paper [2]
            ("{h(1..10,1..10-2)}.", "#true -> forall N0$ N1$ ( 1 <= N0$ <= 10 and (1 <= N1$ <= 10-2) -> (h(N0$, N1$) or not h(N0$, N1$)))" ), // Inspired by Tiling example
            ("{ place(X,Y, T) } :- X = 1..10, Y = 1..10, T = 1..3.",
            "forall X$i Y$i T$i ((1 <= X$i <= 10 and (1 <= Y$i <= 10) and (1 <= T$i  <= 3)) -> (place(X$i, Y$i, T$i) or not place(X$i, Y$i, T$i)))") // Inspired by Tiling
        ] {
            let rule = source.parse().unwrap();
            let natural = natural_rule(&rule).unwrap();
            let natural_string = natural.to_string();
            let target_formula: fol::Formula = target.parse().unwrap();
            let target = target_formula.to_string();
            assert_eq!(natural, target_formula,
            "assertion `natural_rule({rule}) == target` failed:\n natural:\n{natural_string:?}\n target:\n{target:?}",
            );

        }
    }

    #[test]
    fn test_irregular_rule() {
        for rule in [
            "p(1..a).",
            "p(2/5).",
            "p(X) :- X <= 3..5.",
            "p(X) :- X = 5*(2..3).",
            " :- X..5 = 3..5.",
        ] {
            let rule = rule.parse().unwrap();
            println!("{:?}", natural_rule(&rule));
            assert!(
                natural_rule(&rule).is_none(),
                "assertion `natural_rule({rule}) is None` failed.",
            );
        }
    }
}

// TODO: add function for mu translation
// TODO: make it into command line option (add further option to enum)
// TODO: open PR and request review from Tobias, Zach
// TODO: natural_head_atom test cases
