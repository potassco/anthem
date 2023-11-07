use crate::syntax_tree::{asp, fol};
use regex::Regex;
use std::collections::HashSet;
//use std::collections::hash_map::Entry;

use crate::syntax_tree;

pub fn choose_fresh_global_variables(program: &asp::Program) -> Vec<String> {
    let mut max_arity = 0;
    let mut head_arity;
    for rule in program.rules.iter() {
        head_arity = rule.head.get_arity();
        if head_arity > max_arity {
            max_arity = head_arity;
        }
    }
    let mut max_taken_var = 0;
    let taken_vars = program.get_variables();
    let re = Regex::new(r"^V(?<number>[0-9]*)$").unwrap();
    for var in taken_vars {
        match re.captures(&var) {
            Some(caps) => {
                let taken: usize = (&caps["number"]).parse().unwrap_or_else(|_| 0);
                if taken > max_taken_var {
                    max_taken_var = taken;
                }
            }
            None => {}
        }
    }
    let mut globals = Vec::<String>::new();
    for i in 1..max_arity + 1 {
        let mut v: String = "V".to_owned();
        let counter: &str = &(max_taken_var + i).to_string();
        v.push_str(counter);
        globals.push(v);
    }
    globals
}

// Choose <arity> variable names by incrementing <variant>, disjoint from <variables>
pub fn choose_fresh_variable_names_v(
    variables: &HashSet<fol::Variable>,
    variant: &str,
    arity: usize,
) -> Vec<String> {
    let mut taken_vars = Vec::<String>::new();
    for var in variables.iter() {
        taken_vars.push(var.name.to_string());
    }
    let mut fresh_vars = Vec::<String>::new();
    let arity_bound = match taken_vars.contains(&variant.to_string()) {
        true => arity + 1,
        false => {
            fresh_vars.push(variant.to_string());
            arity
        }
    };
    for n in 1..arity_bound {
        let mut candidate: String = variant.to_owned();
        let number: &str = &n.to_string();
        candidate.push_str(number);
        let mut m = n;
        while taken_vars.contains(&candidate) || fresh_vars.contains(&candidate) {
            candidate = variant.to_owned();
            m += 1;
            let number = &m.to_string();
            candidate.push_str(number);
        }
        fresh_vars.push(candidate.to_string());
    }
    fresh_vars
}

// Z = t
fn construct_equality_formula(term: asp::Term, z: fol::Variable) -> fol::Formula {
    let z_var_term = match z.sort {
        fol::Sort::General => fol::GeneralTerm::GeneralVariable(z.name.into()),
        fol::Sort::Integer => fol::GeneralTerm::IntegerTerm(fol::IntegerTerm::BasicIntegerTerm(
            fol::BasicIntegerTerm::IntegerVariable(z.name.into()),
        )),
    };

    let rhs = match term {
        asp::Term::PrecomputedTerm(t) => match t {
            asp::PrecomputedTerm::Infimum => fol::GeneralTerm::IntegerTerm(
                fol::IntegerTerm::BasicIntegerTerm(fol::BasicIntegerTerm::Infimum),
            ),
            asp::PrecomputedTerm::Supremum => fol::GeneralTerm::IntegerTerm(
                fol::IntegerTerm::BasicIntegerTerm(fol::BasicIntegerTerm::Supremum),
            ),
            asp::PrecomputedTerm::Numeral(i) => fol::GeneralTerm::IntegerTerm(
                fol::IntegerTerm::BasicIntegerTerm(fol::BasicIntegerTerm::Numeral(i.into())),
            ),
            asp::PrecomputedTerm::Symbol(s) => fol::GeneralTerm::Symbol(s.into()),
        },
        asp::Term::Variable(v) => fol::GeneralTerm::GeneralVariable(v.0),
        _ => todo!(), // Error
    };

    let valtz = fol::Formula::AtomicFormula(fol::AtomicFormula::Comparison(fol::Comparison {
        term: z_var_term,
        guards: vec![fol::Guard {
            relation: fol::Relation::Equal,
            term: rhs,
        }],
    }));
    valtz
}

// +,-,*
// exists I J (Z = I op J & val_t1(I) & val_t2(J))
fn construct_total_function_formula(
    valti: fol::Formula,
    valtj: fol::Formula,
    binop: asp::BinaryOperator,
    i_var: fol::Variable,
    j_var: fol::Variable,
    z: fol::Variable,
) -> fol::Formula {
    let i = i_var.name;
    let j = j_var.name;
    let z_var_term = match z.sort {
        fol::Sort::General => fol::GeneralTerm::GeneralVariable(z.name.into()),
        fol::Sort::Integer => fol::GeneralTerm::IntegerTerm(fol::IntegerTerm::BasicIntegerTerm(
            fol::BasicIntegerTerm::IntegerVariable(z.name.into()),
        )),
    };
    let zequals = fol::Formula::AtomicFormula(fol::AtomicFormula::Comparison(fol::Comparison {
        // Z = I binop J
        term: z_var_term,
        guards: vec![fol::Guard {
            relation: fol::Relation::Equal,
            term: fol::GeneralTerm::IntegerTerm(fol::IntegerTerm::BinaryOperation {
                op: match binop {
                    asp::BinaryOperator::Add => fol::BinaryOperator::Add,
                    asp::BinaryOperator::Subtract => fol::BinaryOperator::Subtract,
                    asp::BinaryOperator::Multiply => fol::BinaryOperator::Multiply,
                    _ => todo!(), // More error handling
                },
                lhs: fol::IntegerTerm::BasicIntegerTerm(fol::BasicIntegerTerm::IntegerVariable(
                    i.clone(),
                ))
                .into(),
                rhs: fol::IntegerTerm::BasicIntegerTerm(fol::BasicIntegerTerm::IntegerVariable(
                    j.clone(),
                ))
                .into(),
            }),
        }],
    }));
    fol::Formula::QuantifiedFormula {
        quantification: fol::Quantification {
            quantifier: fol::Quantifier::Exists,
            variables: vec![
                fol::Variable {
                    name: i.into(),
                    sort: fol::Sort::Integer,
                },
                fol::Variable {
                    name: j.into(),
                    sort: fol::Sort::Integer,
                },
            ],
        },
        formula: fol::Formula::BinaryFormula {
            connective: fol::BinaryConnective::Conjunction,
            lhs: fol::Formula::BinaryFormula {
                connective: fol::BinaryConnective::Conjunction,
                lhs: zequals.into(),
                rhs: valti.into(),
            }
            .into(),
            rhs: valtj.into(),
        }
        .into(),
    }
}

// Division, modulo
fn construct_partial_function_formula(
    valti: fol::Formula,
    valtj: fol::Formula,
    binop: asp::BinaryOperator,
    i_var: fol::Variable,
    j_var: fol::Variable,
    z: fol::Variable,
) -> fol::Formula {
    let i = i_var.name;
    let j = j_var.name;

    let mut taken_vars = HashSet::<fol::Variable>::new();
    for var in valti.get_variables().iter() {
        taken_vars.insert(fol::Variable {
            name: var.to_string(),
            sort: fol::Sort::General,
        });
    }
    for var in valtj.get_variables().iter() {
        taken_vars.insert(fol::Variable {
            name: var.to_string(),
            sort: fol::Sort::General,
        });
    }

    let z_var_term = match z.sort {
        fol::Sort::General => fol::GeneralTerm::GeneralVariable(z.name.into()),
        fol::Sort::Integer => fol::GeneralTerm::IntegerTerm(fol::IntegerTerm::BasicIntegerTerm(
            fol::BasicIntegerTerm::IntegerVariable(z.name.into()),
        )),
    };

    // I = J * Q + R
    let qvar = choose_fresh_variable_names_v(&taken_vars, "Q", 1)
        .pop()
        .unwrap();
    let rvar = choose_fresh_variable_names_v(&taken_vars, "R", 1)
        .pop()
        .unwrap();
    let iequals = fol::Formula::AtomicFormula(fol::AtomicFormula::Comparison(fol::Comparison {
        term: fol::GeneralTerm::IntegerTerm(fol::IntegerTerm::BasicIntegerTerm(
            fol::BasicIntegerTerm::IntegerVariable(i.clone()),
        )),
        guards: vec![fol::Guard {
            relation: fol::Relation::Equal,
            term: fol::GeneralTerm::IntegerTerm(fol::IntegerTerm::BinaryOperation {
                op: fol::BinaryOperator::Add,
                lhs: fol::IntegerTerm::BinaryOperation {
                    op: fol::BinaryOperator::Multiply,
                    lhs: fol::IntegerTerm::BasicIntegerTerm(
                        fol::BasicIntegerTerm::IntegerVariable(j.clone()),
                    )
                    .into(),
                    rhs: fol::IntegerTerm::BasicIntegerTerm(
                        fol::BasicIntegerTerm::IntegerVariable(qvar.clone().into()),
                    )
                    .into(),
                }
                .into(),
                rhs: fol::IntegerTerm::BasicIntegerTerm(fol::BasicIntegerTerm::IntegerVariable(
                    rvar.clone().into(),
                ))
                .into(),
            }),
        }],
    }));

    // J != 0 & R >= 0 & R < Q
    let conditions = fol::Formula::BinaryFormula {
        connective: fol::BinaryConnective::Conjunction,
        lhs: fol::Formula::BinaryFormula {
            connective: fol::BinaryConnective::Conjunction,
            lhs: fol::Formula::AtomicFormula(fol::AtomicFormula::Comparison(fol::Comparison {
                term: fol::GeneralTerm::IntegerTerm(fol::IntegerTerm::BasicIntegerTerm(
                    fol::BasicIntegerTerm::IntegerVariable(j.clone()),
                )),
                guards: vec![fol::Guard {
                    relation: fol::Relation::NotEqual,
                    term: fol::GeneralTerm::IntegerTerm(fol::IntegerTerm::BasicIntegerTerm(
                        fol::BasicIntegerTerm::Numeral(0),
                    )),
                }],
            }))
            .into(),
            rhs: fol::Formula::AtomicFormula(fol::AtomicFormula::Comparison(fol::Comparison {
                term: fol::GeneralTerm::IntegerTerm(fol::IntegerTerm::BasicIntegerTerm(
                    fol::BasicIntegerTerm::IntegerVariable(rvar.clone().into()),
                )),
                guards: vec![fol::Guard {
                    relation: fol::Relation::GreaterEqual,
                    term: fol::GeneralTerm::IntegerTerm(fol::IntegerTerm::BasicIntegerTerm(
                        fol::BasicIntegerTerm::Numeral(0),
                    )),
                }],
            }))
            .into(),
        }
        .into(),
        rhs: fol::Formula::AtomicFormula(fol::AtomicFormula::Comparison(fol::Comparison {
            term: fol::GeneralTerm::IntegerTerm(fol::IntegerTerm::BasicIntegerTerm(
                fol::BasicIntegerTerm::IntegerVariable(rvar.clone().into()),
            )),
            guards: vec![fol::Guard {
                relation: fol::Relation::Less,
                term: fol::GeneralTerm::IntegerTerm(fol::IntegerTerm::BasicIntegerTerm(
                    fol::BasicIntegerTerm::IntegerVariable(qvar.clone().into()),
                )),
            }],
        }))
        .into(),
    };

    // val_t1(I) & val_t2(J)
    let inner_vals = fol::Formula::BinaryFormula {
        connective: fol::BinaryConnective::Conjunction,
        lhs: valti.into(),
        rhs: valtj.into(),
    };

    // (( I = J * Q + R ) & ( val_t1(I) & val_t2(J) )) & ( J != 0 & R >= 0 & R < Q )
    let subformula = {
        fol::Formula::BinaryFormula {
            connective: fol::BinaryConnective::Conjunction,
            lhs: fol::Formula::BinaryFormula {
                connective: fol::BinaryConnective::Conjunction,
                lhs: iequals.into(),
                rhs: inner_vals.into(),
            }
            .into(),
            rhs: conditions.into(),
        }
    };

    // Z = Q or Z = R
    let zequals = match binop {
        asp::BinaryOperator::Divide => {
            fol::Formula::AtomicFormula(fol::AtomicFormula::Comparison(fol::Comparison {
                term: z_var_term,
                guards: vec![fol::Guard {
                    relation: fol::Relation::Equal,
                    term: fol::GeneralTerm::IntegerTerm(fol::IntegerTerm::BasicIntegerTerm(
                        fol::BasicIntegerTerm::IntegerVariable(qvar.clone().into()),
                    )),
                }],
            }))
        }
        asp::BinaryOperator::Modulo => {
            fol::Formula::AtomicFormula(fol::AtomicFormula::Comparison(fol::Comparison {
                term: z_var_term,
                guards: vec![fol::Guard {
                    relation: fol::Relation::Equal,
                    term: fol::GeneralTerm::IntegerTerm(fol::IntegerTerm::BasicIntegerTerm(
                        fol::BasicIntegerTerm::IntegerVariable(rvar.clone().into()),
                    )),
                }],
            }))
        }
        _ => todo!(), // Error
    };

    fol::Formula::QuantifiedFormula {
        quantification: fol::Quantification {
            quantifier: fol::Quantifier::Exists,
            variables: vec![
                fol::Variable {
                    name: i.into(),
                    sort: fol::Sort::Integer,
                },
                fol::Variable {
                    name: j.into(),
                    sort: fol::Sort::Integer,
                },
                fol::Variable {
                    name: qvar.into(),
                    sort: fol::Sort::Integer,
                },
                fol::Variable {
                    name: rvar.into(),
                    sort: fol::Sort::Integer,
                },
            ],
        },
        formula: fol::Formula::BinaryFormula {
            connective: fol::BinaryConnective::Conjunction,
            lhs: subformula.into(),
            rhs: zequals.into(),
        }
        .into(),
    }
}

// t1..t2
fn construct_interval_formula(
    valti: fol::Formula,
    valtj: fol::Formula,
    i_var: fol::Variable,
    j_var: fol::Variable,
    k_var: fol::Variable,
    z: fol::Variable,
) -> fol::Formula {
    let z_var_term = match z.sort {
        fol::Sort::General => fol::GeneralTerm::GeneralVariable(z.name.into()),
        fol::Sort::Integer => fol::GeneralTerm::IntegerTerm(fol::IntegerTerm::BasicIntegerTerm(
            fol::BasicIntegerTerm::IntegerVariable(z.name.into()),
        )),
    };

    // I <= K <= J
    let range = fol::Formula::AtomicFormula(fol::AtomicFormula::Comparison(fol::Comparison {
        term: fol::GeneralTerm::IntegerTerm(fol::IntegerTerm::BasicIntegerTerm(
            fol::BasicIntegerTerm::IntegerVariable(i_var.name.clone().into()),
        )),
        guards: vec![
            fol::Guard {
                relation: fol::Relation::LessEqual,
                term: fol::GeneralTerm::IntegerTerm(fol::IntegerTerm::BasicIntegerTerm(
                    fol::BasicIntegerTerm::IntegerVariable(k_var.name.clone().into()),
                )),
            },
            fol::Guard {
                relation: fol::Relation::LessEqual,
                term: fol::GeneralTerm::IntegerTerm(fol::IntegerTerm::BasicIntegerTerm(
                    fol::BasicIntegerTerm::IntegerVariable(j_var.name.clone().into()),
                )),
            },
        ],
    }));

    // val_t1(I) & val_t2(J) & Z = k
    let subformula = fol::Formula::BinaryFormula {
        connective: fol::BinaryConnective::Conjunction,
        lhs: fol::Formula::BinaryFormula {
            connective: fol::BinaryConnective::Conjunction,
            lhs: valti.into(),
            rhs: valtj.into(),
        }
        .into(),
        rhs: fol::Formula::AtomicFormula(fol::AtomicFormula::Comparison(fol::Comparison {
            term: z_var_term,
            guards: vec![fol::Guard {
                relation: fol::Relation::Equal,
                term: fol::GeneralTerm::IntegerTerm(fol::IntegerTerm::BasicIntegerTerm(
                    fol::BasicIntegerTerm::IntegerVariable(k_var.name.clone().into()),
                )),
            }],
        }))
        .into(),
    };

    fol::Formula::QuantifiedFormula {
        quantification: fol::Quantification {
            quantifier: fol::Quantifier::Exists,
            variables: vec![i_var.clone(), j_var.clone(), k_var.clone()],
        },
        formula: fol::Formula::BinaryFormula {
            connective: fol::BinaryConnective::Conjunction,
            lhs: subformula.into(),
            rhs: range.into(),
        }
        .into(),
    }
}

// val_t(Z)
pub fn val(t: asp::Term, z: fol::Variable) -> fol::Formula {
    let mut taken_vars = HashSet::<fol::Variable>::new();
    for var in t.get_variables().iter() {
        taken_vars.insert(fol::Variable {
            name: var.to_string(),
            sort: fol::Sort::General,
        });
    }
    taken_vars.insert(z.clone());

    let mut fresh_ivar = choose_fresh_variable_names_v(&taken_vars, "I", 1);
    let mut fresh_jvar = choose_fresh_variable_names_v(&taken_vars, "J", 1);
    let mut fresh_kvar = choose_fresh_variable_names_v(&taken_vars, "K", 1);

    // Fresh integer variables
    let var1 = fol::Variable {
        name: fresh_ivar.pop().unwrap().into(),
        sort: fol::Sort::Integer,
    };
    let var2 = fol::Variable {
        name: fresh_jvar.pop().unwrap().into(),
        sort: fol::Sort::Integer,
    };
    let var3 = fol::Variable {
        name: fresh_kvar.pop().unwrap().into(),
        sort: fol::Sort::Integer,
    };
    match t {
        asp::Term::PrecomputedTerm(_) | asp::Term::Variable(_) => construct_equality_formula(t, z),
        asp::Term::UnaryOperation { op, arg } => {
            match op {
                asp::UnaryOperator::Negative => {
                    let lhs = asp::Term::PrecomputedTerm(asp::PrecomputedTerm::Numeral(0)); // Shorthand for 0 - t
                    let valti = val(lhs, var1.clone()); // val_t1(I)
                    let valtj = val(*arg, var2.clone()); // val_t2(J)
                    construct_total_function_formula(
                        valti,
                        valtj,
                        asp::BinaryOperator::Subtract,
                        var1.clone(),
                        var2.clone(),
                        z,
                    )
                }
            }
        }
        asp::Term::BinaryOperation { op, lhs, rhs } => {
            let valti = val(*lhs, var1.clone()); // val_t1(I)
            let valtj = val(*rhs, var2.clone()); // val_t2(J)
            match op {
                syntax_tree::asp::BinaryOperator::Add => construct_total_function_formula(
                    valti,
                    valtj,
                    asp::BinaryOperator::Add,
                    var1.clone(),
                    var2.clone(),
                    z,
                ),
                syntax_tree::asp::BinaryOperator::Subtract => construct_total_function_formula(
                    valti,
                    valtj,
                    asp::BinaryOperator::Subtract,
                    var1.clone(),
                    var2.clone(),
                    z,
                ),
                syntax_tree::asp::BinaryOperator::Multiply => construct_total_function_formula(
                    valti,
                    valtj,
                    asp::BinaryOperator::Multiply,
                    var1.clone(),
                    var2.clone(),
                    z,
                ),
                syntax_tree::asp::BinaryOperator::Divide => construct_partial_function_formula(
                    valti,
                    valtj,
                    asp::BinaryOperator::Divide,
                    var1.clone(),
                    var2.clone(),
                    z,
                ),
                syntax_tree::asp::BinaryOperator::Modulo => construct_partial_function_formula(
                    valti,
                    valtj,
                    asp::BinaryOperator::Modulo,
                    var1.clone(),
                    var2.clone(),
                    z,
                ),
                syntax_tree::asp::BinaryOperator::Interval => construct_interval_formula(
                    valti,
                    valtj,
                    var1.clone(),
                    var2.clone(),
                    var3.clone(),
                    z,
                ),
            }
        }
    }
}

// val_t1(Z1) & val_t2(Z2) & ... & val_tn(Zn)
pub fn valtz(terms: Vec<asp::Term>, variables: Vec<fol::Variable>) -> fol::Formula {
    let mut formulas: Vec<fol::Formula> = Vec::with_capacity(terms.len() as usize);
    for (i, t) in terms.iter().enumerate() {
        let val_ti_zi = val(t.clone(), variables[i].clone());
        formulas.push(val_ti_zi);
    }
    let first_formula = formulas.pop().unwrap();
    conjoin((formulas, first_formula.clone()))
}

// Recursively turn a list of formulas into a conjunction tree
pub fn conjoin(mut pair: (Vec<fol::Formula>, fol::Formula)) -> fol::Formula {
    if pair.0.len() == 0 {
        pair.1
    } else {
        let partial = fol::Formula::BinaryFormula {
            connective: fol::BinaryConnective::Conjunction,
            lhs: pair.0.pop().unwrap().into(),
            rhs: pair.1.into(),
        }
        .into();
        conjoin((pair.0, partial))
    }
}

// Recursively turn a list of formulas into a tree of disjunctions
pub fn disjoin(mut pair: (Vec<fol::Formula>, fol::Formula)) -> fol::Formula {
    if pair.0.len() == 0 {
        pair.1
    } else {
        let partial = fol::Formula::BinaryFormula {
            connective: fol::BinaryConnective::Disjunction,
            lhs: pair.0.pop().unwrap().into(),
            rhs: pair.1.into(),
        }
        .into();
        disjoin((pair.0, partial))
    }
}

// Translate a body literal or comparison
pub fn tau_b(f: asp::AtomicFormula) -> fol::Formula {
    let mut taken_vars = HashSet::<fol::Variable>::new();
    for var in f.get_variables().iter() {
        taken_vars.insert(fol::Variable {
            name: var.to_string(),
            sort: fol::Sort::General,
        });
    }
    match f {
        asp::AtomicFormula::Literal(l) => {
            let atom = l.atom;
            let terms = atom.terms;
            let arity = terms.len();
            let varnames = choose_fresh_variable_names_v(&taken_vars, "Z", arity);

            // Compute val_t1(Z1) & val_t2(Z2) & ... & val_tk(Zk)
            if arity > 0 {
                let mut var_terms: Vec<fol::GeneralTerm> = Vec::with_capacity(arity as usize);
                let mut var_vars: Vec<fol::Variable> = Vec::with_capacity(arity as usize);
                let mut valtz_vec: Vec<fol::Formula> = Vec::with_capacity(arity as usize);
                for (i, t) in terms.iter().enumerate() {
                    let var = fol::Variable {
                        sort: fol::Sort::General,
                        name: varnames[i].clone(),
                    };
                    valtz_vec.push(val(t.clone(), var.clone()));
                    var_terms.push(fol::GeneralTerm::GeneralVariable(varnames[i].clone()));
                    var_vars.push(var);
                }
                let first_formula = valtz_vec.pop().unwrap();
                let valtz = conjoin((valtz_vec, first_formula));

                // Compute p(Z1, Z2, ..., Zk)
                let p_zk = fol::Formula::AtomicFormula(fol::AtomicFormula::Atom(fol::Atom {
                    predicate: atom.predicate,
                    terms: var_terms,
                }));

                // Compute tau^b(B)
                match l.sign {
                    syntax_tree::asp::Sign::NoSign => fol::Formula::QuantifiedFormula {
                        quantification: fol::Quantification {
                            quantifier: fol::Quantifier::Exists,
                            variables: var_vars,
                        },
                        formula: fol::Formula::BinaryFormula {
                            connective: fol::BinaryConnective::Conjunction,
                            lhs: valtz.into(),
                            rhs: p_zk.into(),
                        }
                        .into(),
                    },
                    syntax_tree::asp::Sign::Negation => fol::Formula::QuantifiedFormula {
                        quantification: fol::Quantification {
                            quantifier: fol::Quantifier::Exists,
                            variables: var_vars,
                        },
                        formula: fol::Formula::BinaryFormula {
                            connective: fol::BinaryConnective::Conjunction,
                            lhs: valtz.into(),
                            rhs: fol::Formula::UnaryFormula {
                                connective: fol::UnaryConnective::Negation,
                                formula: p_zk.into(),
                            }
                            .into(),
                        }
                        .into(),
                    },
                    syntax_tree::asp::Sign::DoubleNegation => fol::Formula::QuantifiedFormula {
                        quantification: fol::Quantification {
                            quantifier: fol::Quantifier::Exists,
                            variables: var_vars,
                        },
                        formula: fol::Formula::BinaryFormula {
                            connective: fol::BinaryConnective::Conjunction,
                            lhs: valtz.into(),
                            rhs: fol::Formula::UnaryFormula {
                                connective: fol::UnaryConnective::Negation,
                                formula: fol::Formula::UnaryFormula {
                                    connective: fol::UnaryConnective::Negation,
                                    formula: p_zk.into(),
                                }
                                .into(),
                            }
                            .into(),
                        }
                        .into(),
                    },
                }
            } else {
                match l.sign {
                    syntax_tree::asp::Sign::NoSign => {
                        fol::Formula::AtomicFormula(fol::AtomicFormula::Atom(fol::Atom {
                            predicate: atom.predicate,
                            terms: vec![],
                        }))
                    }
                    syntax_tree::asp::Sign::Negation => fol::Formula::UnaryFormula {
                        connective: fol::UnaryConnective::Negation,
                        formula: fol::Formula::AtomicFormula(fol::AtomicFormula::Atom(fol::Atom {
                            predicate: atom.predicate,
                            terms: vec![],
                        }))
                        .into(),
                    },
                    syntax_tree::asp::Sign::DoubleNegation => fol::Formula::UnaryFormula {
                        connective: fol::UnaryConnective::Negation,
                        formula: fol::Formula::UnaryFormula {
                            connective: fol::UnaryConnective::Negation,
                            formula: fol::Formula::AtomicFormula(fol::AtomicFormula::Atom(
                                fol::Atom {
                                    predicate: atom.predicate,
                                    terms: vec![],
                                },
                            ))
                            .into(),
                        }
                        .into(),
                    },
                }
            }
        }
        asp::AtomicFormula::Comparison(c) => {
            let varnames = choose_fresh_variable_names_v(&taken_vars, "Z", 2);

            // Compute val_t1(Z1) & val_t2(Z2)
            let term_z1 = fol::GeneralTerm::GeneralVariable(varnames[0].clone());
            let term_z2 = fol::GeneralTerm::GeneralVariable(varnames[1].clone());
            let var_z1 = fol::Variable {
                sort: fol::Sort::General,
                name: varnames[0].clone(),
            };
            let var_z2 = fol::Variable {
                sort: fol::Sort::General,
                name: varnames[1].clone(),
            };
            let valtz = conjoin((vec![val(c.lhs, var_z1.clone())], val(c.rhs, var_z2.clone())));

            // Compute Z1 rel Z2
            let z1_rel_z2 =
                fol::Formula::AtomicFormula(fol::AtomicFormula::Comparison(fol::Comparison {
                    term: term_z1,
                    guards: vec![fol::Guard {
                        relation: match c.relation {
                            asp::Relation::Equal => fol::Relation::Equal,
                            asp::Relation::NotEqual => fol::Relation::NotEqual,
                            asp::Relation::Greater => fol::Relation::Greater,
                            asp::Relation::Less => fol::Relation::Less,
                            asp::Relation::GreaterEqual => fol::Relation::GreaterEqual,
                            asp::Relation::LessEqual => fol::Relation::LessEqual,
                        },
                        term: term_z2,
                    }],
                }));

            fol::Formula::QuantifiedFormula {
                quantification: fol::Quantification {
                    quantifier: fol::Quantifier::Exists,
                    variables: vec![var_z1, var_z2],
                },
                formula: fol::Formula::BinaryFormula {
                    connective: fol::BinaryConnective::Conjunction,
                    lhs: valtz.into(),
                    rhs: z1_rel_z2.into(),
                }
                .into(),
            }
        }
    }
}

// Translate a rule body
pub fn tau_body(b: asp::Body) -> fol::Formula {
    let mut formulas = Vec::<fol::Formula>::new();
    for f in b.formulas.iter() {
        formulas.push(tau_b(f.clone()));
    }
    let first_formula = formulas.pop().unwrap();
    conjoin((formulas, first_formula.clone()))
}

//pub fn tau_star_rule(p: asp::Rule) -> fol::Formula {
//   todo!()
//}

// For each rule, produce a formula: forall G V ( val_t(V) & tau_body(Body) -> p(V) )
// Where G is all variables from the original rule
// and V is the set of fresh variables replacing t within p
pub fn tau_star_program(p: asp::Program) -> fol::Theory {
    let globals = choose_fresh_global_variables(&p);
    let mut formulas: Vec<fol::Formula> = vec![]; // { forall G V ( val_t(V) & tau^B(Body) -> p(V) ), ... }
    for r in p.rules.iter() {
        let mut propositional_fact_edge_case = false; // Very rarely, tau*(Pi) might produce a formula of form "p." rather than an implication "forall V (F -> G)"
        let head_symbol: Option<String> = r.get_head_symbol(); // p
        let head_arity = r.head.get_arity(); // n
        let gvars = r.get_variables(); // G
        match head_symbol {
            Some(_) => {
                let fvars = &globals[0..head_arity]; // V, |V| = n
                let head_pred = r.head.get_predicate();
                match head_pred {
                    Some(p) => {
                        let new_head;
                        let core_lhs;
                        if head_arity > 0 {
                            // first-order case
                            let head_terms = r.head.get_terms().unwrap(); // p(t) becomes p(V)
                            let mut new_terms = Vec::<fol::GeneralTerm>::new();
                            let mut fo_vars = Vec::<fol::Variable>::new();
                            for (i, _) in head_terms.iter().enumerate() {
                                let fol_var = fol::Variable {
                                    name: fvars[i].to_string(),
                                    sort: fol::Sort::General,
                                };
                                let fol_term =
                                    fol::GeneralTerm::GeneralVariable(fvars[i].to_string());
                                fo_vars.push(fol_var);
                                new_terms.push(fol_term);
                            }
                            let valtz = valtz(head_terms, fo_vars); // val_t(V)
                            new_head =
                                fol::Formula::AtomicFormula(fol::AtomicFormula::Atom(fol::Atom {
                                    predicate: p,
                                    terms: new_terms,
                                })); // p(V)
                            if r.body.formulas.len() == 0 {
                                // Rule is a fact p(t)
                                core_lhs = valtz;
                            } else {
                                core_lhs = fol::Formula::BinaryFormula {
                                    connective: fol::BinaryConnective::Conjunction,
                                    lhs: valtz.into(),
                                    rhs: tau_body(r.body.clone()).into(), // tau^B(Body)
                                };
                            }
                        } else {
                            // Propositional case
                            new_head =
                                fol::Formula::AtomicFormula(fol::AtomicFormula::Atom(fol::Atom {
                                    predicate: p,
                                    terms: vec![],
                                }));
                            if r.body.formulas.len() == 0 {
                                propositional_fact_edge_case = true;
                                core_lhs = fol::Formula::AtomicFormula(fol::AtomicFormula::Falsity);
                            // This assignment is never used
                            } else {
                                core_lhs = tau_body(r.body.clone());
                            }
                        }
                        if propositional_fact_edge_case {
                            formulas.push(new_head);
                        } else {
                            let imp_lhs: Option<fol::Formula> = match r.head {
                                asp::Head::Basic(_) => Some(core_lhs), // val_t(V) & tau^B(Body)
                                asp::Head::Choice(_) => Some(fol::Formula::BinaryFormula {
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
                                }),
                                _ => None,
                            };
                            let imp = fol::Formula::BinaryFormula {
                                connective: fol::BinaryConnective::Implication,
                                lhs: imp_lhs.unwrap().into(),
                                rhs: new_head.into(),
                            }; // val_t(V) & tau^B(Body) -> p(V)
                            let mut gv = Vec::<fol::Variable>::new();
                            for var in gvars.iter() {
                                gv.push(fol::Variable {
                                    sort: fol::Sort::General,
                                    name: var.to_string(),
                                });
                            }
                            for var in fvars.iter() {
                                gv.push(fol::Variable {
                                    sort: fol::Sort::General,
                                    name: var.to_string(),
                                });
                            }
                            if gv.len() > 0 {
                                // First-order case
                                let formula = fol::Formula::QuantifiedFormula {
                                    quantification: fol::Quantification {
                                        quantifier: fol::Quantifier::Forall,
                                        variables: gv,
                                    },
                                    formula: imp.into(),
                                };
                                formulas.push(formula); // forall G V ( val_t(V) & tau^B(Body) -> p(V) )
                            } else {
                                // G V is empty
                                formulas.push(imp);
                            }
                        }
                    }
                    None => {}
                };
            }
            None => {
                let mut gv = Vec::<fol::Variable>::new();
                for var in gvars.iter() {
                    gv.push(fol::Variable {
                        sort: fol::Sort::General,
                        name: var.to_string(),
                    });
                }
                let imp = fol::Formula::BinaryFormula {
                    connective: fol::BinaryConnective::Implication,
                    lhs: tau_body(r.body.clone()).into(),
                    rhs: fol::Formula::AtomicFormula(fol::AtomicFormula::Falsity).into(),
                }; // tau^B(Body) -> \bot
                if gv.len() > 0 {
                    let formula = fol::Formula::QuantifiedFormula {
                        quantification: fol::Quantification {
                            quantifier: fol::Quantifier::Forall,
                            variables: gv,
                        },
                        formula: imp.into(),
                    }; // forall G ( tau^B(Body) -> \bot )
                    formulas.push(formula);
                } else {
                    formulas.push(imp);
                }
            }
        }
    }
    fol::Theory { formulas: formulas }
}

#[cfg(test)]
mod tests {
    use crate::formatting;
    use crate::{syntax_tree::asp, syntax_tree::fol};

    #[test]
    pub fn val_test1() {
        let term: asp::Term = "X+1".parse().unwrap();
        let var = fol::Variable {
            name: "Z1".to_string(),
            sort: fol::Sort::General,
        };
        let val_term_var = super::val(term, var);

        let target: fol::Formula = "exists I$i J$i (Z1$g = I$i + J$i and I$i = X and J$i = 1)"
            .parse()
            .unwrap();
        assert_eq!(
            format!("{}", formatting::fol::default::Format(&val_term_var)),
            format!("{}", formatting::fol::default::Format(&target))
        );
    }

    #[test]
    pub fn val_test2() {
        let term: asp::Term = "3-5".parse().unwrap();
        let var = fol::Variable {
            name: "Z1".to_string(),
            sort: fol::Sort::General,
        };
        let val_term_var = super::val(term, var);

        let target: fol::Formula = "exists I$i J$i (Z1$g = I$i - J$i and I$i = 3 and J$i = 5)"
            .parse()
            .unwrap();
        assert_eq!(
            format!("{}", formatting::fol::default::Format(&val_term_var)),
            format!("{}", formatting::fol::default::Format(&target))
        );
    }

    #[test]
    pub fn val_test3() {
        let term: asp::Term = "Xanadu/Yak".parse().unwrap();
        let var = fol::Variable {
            name: "Z1".to_string(),
            sort: fol::Sort::General,
        };
        let val_term_var = super::val(term, var);

        let target: fol::Formula =
            "exists I$i J$i Q$i R$i (I$i = J$i * Q$i + R$i and (I$i = Xanadu and J$i = Yak) and (J$i != 0 and R$i >= 0 and R$i < Q$i) and Z1$g = Q$i)"
                .parse()
                .unwrap();
        assert_eq!(
            format!("{}", formatting::fol::default::Format(&val_term_var)),
            format!("{}", formatting::fol::default::Format(&target))
        );
    }

    #[test]
    pub fn val_test4() {
        let term: asp::Term = "X\\3".parse().unwrap();
        let var = fol::Variable {
            name: "Z1".to_string(),
            sort: fol::Sort::General,
        };
        let val_term_var = super::val(term, var);

        let target: fol::Formula =
            "exists I$i J$i Q$i R$i (I$i = J$i * Q$i + R$i and (I$i = X and J$i = 3) and (J$i != 0 and R$i >= 0 and R$i < Q$i) and Z1$g = R$i)"
                .parse()
                .unwrap();
        assert_eq!(
            format!("{}", formatting::fol::default::Format(&val_term_var)),
            format!("{}", formatting::fol::default::Format(&target))
        );
    }

    #[test]
    pub fn val_test5() {
        let term: asp::Term = "X..Y".parse().unwrap();
        let var = fol::Variable {
            name: "Z".to_string(),
            sort: fol::Sort::General,
        };
        let val_term_var = super::val(term, var);

        let target: fol::Formula =
            "exists I$i J$i K$i (I$i = X and J$i = Y and Z$g = K$i and I$i <= K$i <= J$i)"
                .parse()
                .unwrap();
        assert_eq!(
            format!("{}", formatting::fol::default::Format(&val_term_var)),
            format!("{}", formatting::fol::default::Format(&target))
        );
    }

    #[test]
    pub fn val_test6() {
        let term: asp::Term = "X+1..Y".parse().unwrap();
        let var = fol::Variable {
            name: "Z1".to_string(),
            sort: fol::Sort::General,
        };
        let val_term_var = super::val(term, var);

        let target: fol::Formula =
            "exists I$i J$i K$i ((exists I1$i J$i (I$i = I1$i + J$i and I1$i = X and J$i = 1)) and J$i = Y and Z1 = K$i and I$i <= K$i <= J$i )"
                .parse()
                .unwrap();
        assert_eq!(
            format!("{}", formatting::fol::default::Format(&val_term_var)),
            format!("{}", formatting::fol::default::Format(&target))
        );
    }

    #[test]
    pub fn tau_b_test1() {
        let atomic: asp::AtomicFormula = "p(t)".parse().unwrap();
        let result: fol::Formula = super::tau_b(atomic);

        let target: fol::Formula = "exists Z (Z = t and p(Z))".parse().unwrap();
        assert_eq!(
            format!("{}", formatting::fol::default::Format(&result)),
            format!("{}", formatting::fol::default::Format(&target))
        );
    }

    #[test]
    pub fn tau_b_test2() {
        let atomic: asp::AtomicFormula = "not p(t)".parse().unwrap();
        let result: fol::Formula = super::tau_b(atomic);

        let target: fol::Formula = "exists Z (Z = t and not p(Z))".parse().unwrap();
        assert_eq!(
            format!("{}", formatting::fol::default::Format(&result)),
            format!("{}", formatting::fol::default::Format(&target))
        );
    }

    #[test]
    pub fn tau_b_test3() {
        let atomic: asp::AtomicFormula = "X < 1..5".parse().unwrap();
        let result: fol::Formula = super::tau_b(atomic);

        let target: fol::Formula =
        "exists Z Z1 (Z = X and exists I$i J$i K$i (I$i = 1 and J$i = 5 and Z1 = K$i and I$i <= K$i <= J$i) and Z < Z1)"
                .parse()
                .unwrap();
        assert_eq!(
            format!("{}", formatting::fol::default::Format(&result)),
            format!("{}", formatting::fol::default::Format(&target))
        );
    }

    #[test]
    pub fn tau_b_test4() {
        let atomic: asp::AtomicFormula = "not not p(t)".parse().unwrap();
        let result: fol::Formula = super::tau_b(atomic);

        let target: fol::Formula = "exists Z (Z = t and not not p(Z))".parse().unwrap();
        assert_eq!(
            format!("{}", formatting::fol::default::Format(&result)),
            format!("{}", formatting::fol::default::Format(&target))
        );
    }

    #[test]
    pub fn tau_b_test5() {
        let atomic: asp::AtomicFormula = "not not x".parse().unwrap();
        let result: fol::Formula = super::tau_b(atomic);

        let target: fol::Formula = "not not x".parse().unwrap();
        assert_eq!(
            format!("{}", formatting::fol::default::Format(&result)),
            format!("{}", formatting::fol::default::Format(&target))
        );
    }

    #[test]
    pub fn tau_b_test6() {
        let atomic: asp::AtomicFormula = "not p(X,5)".parse().unwrap();
        let result: fol::Formula = super::tau_b(atomic);

        let target: fol::Formula = "exists Z Z1 (Z = X and Z1 = 5 and not p(Z,Z1))"
            .parse()
            .unwrap();
        assert_eq!(
            format!("{}", formatting::fol::default::Format(&result)),
            format!("{}", formatting::fol::default::Format(&target))
        );
    }

    #[test]
    pub fn tau_b_test7() {
        let atomic: asp::AtomicFormula = "not p(X,0-5)".parse().unwrap();
        let result: fol::Formula = super::tau_b(atomic);

        let target: fol::Formula = "exists Z Z1 (Z = X and exists I$i J$i (Z1 = I$i - J$i and I$i = 0 and J$i = 5) and not p(Z,Z1))"
            .parse()
            .unwrap();
        assert_eq!(
            format!("{}", formatting::fol::default::Format(&result)),
            format!("{}", formatting::fol::default::Format(&target))
        );
    }

    #[test]
    pub fn tau_b_test8() {
        let atomic: asp::AtomicFormula = "p(X,-1..5)".parse().unwrap();
        let result: fol::Formula = super::tau_b(atomic);

        let target: fol::Formula = "exists Z Z1 (Z = X and exists I$i J$i K$i (I$i = -1 and J$i = 5  and Z1 = K$i and I$i <= K$i <= J$i) and p(Z,Z1))"
            .parse()
            .unwrap();
        assert_eq!(
            format!("{}", formatting::fol::default::Format(&result)),
            format!("{}", formatting::fol::default::Format(&target))
        );
    }

    #[test]
    pub fn tau_b_test9() {
        let atomic: asp::AtomicFormula = "p(X,-(1..5))".parse().unwrap();
        let result: fol::Formula = super::tau_b(atomic);

        let target: fol::Formula = "exists Z Z1 (Z = X and exists I$i J$i (Z1 = I$i - J$i and I$i = 0 and exists I$i J1$i K$i (I$i = 1 and J1$i = 5  and J$i = K$i and I$i <= K$i <= J1$i)) and p(Z,Z1))"
            .parse()
            .unwrap();
        assert_eq!(
            format!("{}", formatting::fol::default::Format(&result)),
            format!("{}", formatting::fol::default::Format(&target))
        );
    }

    #[test]
    pub fn tau_star_test1() {
        let rule1: asp::Rule = "a :- b.".parse().unwrap();
        let rule2: asp::Rule = "a :- c.".parse().unwrap();
        let program = asp::Program {
            rules: vec![rule1, rule2],
        };

        let form1: fol::Formula = "b -> a".parse().unwrap();
        let form2: fol::Formula = "c -> a".parse().unwrap();
        let theory = fol::Theory {
            formulas: vec![form1, form2],
        };

        let result: fol::Theory = super::tau_star_program(program);
        assert_eq!(result, theory);
    }

    #[test]
    pub fn tau_star_test2() {
        let rule1: asp::Rule = "p(a).".parse().unwrap();
        let rule2: asp::Rule = "p(b).".parse().unwrap();
        let rule3: asp::Rule = "q(X,Y) :- p(X), p(Y).".parse().unwrap();
        let program = asp::Program {
            rules: vec![rule1, rule2, rule3],
        };

        let form1: fol::Formula = "forall V1 (V1 = a -> p(V1))".parse().unwrap();
        let form2: fol::Formula = "forall V1 (V1 = b -> p(V1))".parse().unwrap();
        let form3: fol::Formula = "forall X Y V1 V2 (V1 = X and V2 = Y and (exists Z (Z = X and p(Z)) and exists Z (Z = Y and p(Z))) -> q(V1,V2))".parse().unwrap();
        let theory = fol::Theory {
            formulas: vec![form1, form2, form3],
        };

        let result: fol::Theory = super::tau_star_program(program);
        assert_eq!(
            format!("{}", formatting::fol::default::Format(&result)),
            format!("{}", formatting::fol::default::Format(&theory))
        );
    }

    #[test]
    pub fn tau_star_test3() {
        let rule1: asp::Rule = "p.".parse().unwrap();
        let program = asp::Program { rules: vec![rule1] };

        let form1: fol::Formula = "p".parse().unwrap();
        let theory = fol::Theory {
            formulas: vec![form1],
        };

        let result: fol::Theory = super::tau_star_program(program);
        assert_eq!(
            format!("{}", formatting::fol::default::Format(&result)),
            format!("{}", formatting::fol::default::Format(&theory))
        );
    }

    #[test]
    pub fn tau_star_test4() {
        let rule1: asp::Rule = "q :- not p.".parse().unwrap();
        let program = asp::Program { rules: vec![rule1] };

        let form1: fol::Formula = "not p -> q".parse().unwrap();
        let theory = fol::Theory {
            formulas: vec![form1],
        };

        let result: fol::Theory = super::tau_star_program(program);
        assert_eq!(
            format!("{}", formatting::fol::default::Format(&result)),
            format!("{}", formatting::fol::default::Format(&theory))
        );
    }

    #[test]
    pub fn tau_star_test5() {
        let rule1: asp::Rule = "{q(X)} :- p(X).".parse().unwrap();
        let program = asp::Program { rules: vec![rule1] };

        let form1: fol::Formula =
            "forall V1 X (V1 = X and exists Z (Z = X and p(Z)) and not not q(V1) -> q(V1))"
                .parse()
                .unwrap();
        let theory = fol::Theory {
            formulas: vec![form1],
        };

        let result: fol::Theory = super::tau_star_program(program);
        assert_eq!(
            format!("{}", formatting::fol::default::Format(&result)),
            format!("{}", formatting::fol::default::Format(&theory))
        );
    }

    #[test]
    pub fn tau_star_test6() {
        let rule1: asp::Rule = "{q(V)} :- p(V).".parse().unwrap();
        let program = asp::Program { rules: vec![rule1] };

        let form1: fol::Formula =
            "forall V V1 (V1 = V and exists Z (Z = V and p(Z)) and not not q(V1) -> q(V1))"
                .parse()
                .unwrap();
        let theory = fol::Theory {
            formulas: vec![form1],
        };

        let result: fol::Theory = super::tau_star_program(program);
        assert_eq!(
            format!("{}", formatting::fol::default::Format(&result)),
            format!("{}", formatting::fol::default::Format(&theory))
        );
    }

    #[test]
    pub fn tau_star_test7() {
        let rule1: asp::Rule = "{q(V+1)} :- p(V), not q(X).".parse().unwrap();
        let program = asp::Program { rules: vec![rule1] };

        let form1: fol::Formula =
            "forall V V1 X (exists I$i J$i (V1 = I$i + J$i and I$i = V and J$i = 1) and (exists Z (Z = V and p(Z)) and exists Z (Z = X and not q(Z))) and not not q(V1) -> q(V1))"
                .parse()
                .unwrap();
        let theory = fol::Theory {
            formulas: vec![form1],
        };

        let result: fol::Theory = super::tau_star_program(program);
        assert_eq!(
            format!("{}", formatting::fol::default::Format(&result)),
            format!("{}", formatting::fol::default::Format(&theory))
        );
    }

    #[test]
    pub fn tau_star_test8() {
        let rule1: asp::Rule = ":- p(X,3), not q(X,a).".parse().unwrap();
        let program = asp::Program { rules: vec![rule1] };

        let form1: fol::Formula =
            "forall X (exists Z Z1 (Z = X and Z1 = 3 and p(Z,Z1)) and exists Z Z1 (Z = X and Z1 = a and not q(Z,Z1)) -> #false)"
                .parse()
                .unwrap();
        let theory = fol::Theory {
            formulas: vec![form1],
        };

        let result: fol::Theory = super::tau_star_program(program);
        assert_eq!(
            format!("{}", formatting::fol::default::Format(&result)),
            format!("{}", formatting::fol::default::Format(&theory))
        );
    }

    #[test]
    pub fn tau_star_test9() {
        let rule1: asp::Rule = ":- p.".parse().unwrap();
        let program = asp::Program { rules: vec![rule1] };

        let form1: fol::Formula = "p -> #false".parse().unwrap();
        let theory = fol::Theory {
            formulas: vec![form1],
        };

        let result: fol::Theory = super::tau_star_program(program);
        assert_eq!(
            format!("{}", formatting::fol::default::Format(&result)),
            format!("{}", formatting::fol::default::Format(&theory))
        );
    }

    #[test]
    pub fn tau_star_test10() {
        let rule1: asp::Rule = "{p} :- q.".parse().unwrap();
        let program = asp::Program { rules: vec![rule1] };

        let form1: fol::Formula = "q and not not p -> p".parse().unwrap();
        let theory = fol::Theory {
            formulas: vec![form1],
        };

        let result: fol::Theory = super::tau_star_program(program);
        assert_eq!(
            format!("{}", formatting::fol::default::Format(&result)),
            format!("{}", formatting::fol::default::Format(&theory))
        );
    }
}