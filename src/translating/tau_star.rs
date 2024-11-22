use {
    crate::{
        convenience::choose_fresh_variable_names,
        syntax_tree::{asp, fol},
    },
    indexmap::IndexSet,
    lazy_static::lazy_static,
    regex::Regex,
};

lazy_static! {
    static ref RE: Regex = Regex::new(r"^V(?<number>[0-9]*)$").unwrap();
}

/// Choose fresh variants of `Vn` by incrementing `n`
fn choose_fresh_global_variables(program: &asp::Program) -> Vec<String> {
    let mut max_arity = 0;
    let mut head_arity;
    for rule in program.rules.iter() {
        head_arity = rule.head.arity();
        if head_arity > max_arity {
            max_arity = head_arity;
        }
    }
    let mut max_taken_var = 0;
    let taken_vars = program.variables();
    for var in taken_vars {
        if let Some(caps) = RE.captures(&var.0) {
            let taken: usize = (caps["number"]).parse().unwrap_or(0);
            if taken > max_taken_var {
                max_taken_var = taken;
            }
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

// Z = t
fn construct_equality_formula(term: asp::Term, z: fol::Variable) -> fol::Formula {
    let z_var_term = match z.sort {
        fol::Sort::General => fol::GeneralTerm::Variable(z.name),
        fol::Sort::Integer => fol::GeneralTerm::IntegerTerm(fol::IntegerTerm::Variable(z.name)),
        fol::Sort::Symbol => unreachable!("tau* should not produce variables of the Symbol sort"),
    };

    let rhs = match term {
        asp::Term::PrecomputedTerm(t) => match t {
            asp::PrecomputedTerm::Infimum => fol::GeneralTerm::Infimum,
            asp::PrecomputedTerm::Supremum => fol::GeneralTerm::Supremum,
            asp::PrecomputedTerm::Numeral(i) => {
                fol::GeneralTerm::IntegerTerm(fol::IntegerTerm::Numeral(i))
            }
            asp::PrecomputedTerm::Symbol(s) => {
                fol::GeneralTerm::SymbolicTerm(fol::SymbolicTerm::Symbol(s))
            }
        },
        asp::Term::Variable(v) => fol::GeneralTerm::Variable(v.0),
        _ => unreachable!(
            "equality should be between two variables or a variable and a precomputed term"
        ),
    };

    fol::Formula::AtomicFormula(fol::AtomicFormula::Comparison(fol::Comparison {
        term: z_var_term,
        guards: vec![fol::Guard {
            relation: fol::Relation::Equal,
            term: rhs,
        }],
    }))
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
        fol::Sort::General => fol::GeneralTerm::Variable(z.name),
        fol::Sort::Integer => fol::GeneralTerm::IntegerTerm(fol::IntegerTerm::Variable(z.name)),
        fol::Sort::Symbol => unreachable!("tau* should not produce variables of the Symbol sort"),
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
                    _ => unreachable!("addition, subtraction and multiplication are the only supported total functions"),
                },
                lhs: fol::IntegerTerm::Variable(i.clone()).into(),
                rhs: fol::IntegerTerm::Variable(j.clone()).into(),
            }),
        }],
    }));
    fol::Formula::QuantifiedFormula {
        quantification: fol::Quantification {
            quantifier: fol::Quantifier::Exists,
            variables: vec![
                fol::Variable {
                    name: i,
                    sort: fol::Sort::Integer,
                },
                fol::Variable {
                    name: j,
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

// Integer division. Not Abstract Gringo compliant in negative divisor edge cases.
// Follows the corrected arXiv paper (https://arxiv.org/abs/2008.02025), not the TPLP paper
// Division: exists I J Q R (I = J * Q + R & val_t1(I) & val_t2(J) & J != 0 & R >= 0 & R < J & Z = Q)
// Modulo:   exists I J Q R (I = J * Q + R & val_t1(I) & val_t2(J) & J != 0 & R >= 0 & R < J & Z = R)
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

    let mut taken_vars = IndexSet::<fol::Variable>::new();
    for var in valti.variables().iter() {
        taken_vars.insert(fol::Variable {
            name: var.to_string(),
            sort: fol::Sort::General,
        });
    }
    for var in valtj.variables().iter() {
        taken_vars.insert(fol::Variable {
            name: var.to_string(),
            sort: fol::Sort::General,
        });
    }

    let z_var_term = match z.sort {
        fol::Sort::General => fol::GeneralTerm::Variable(z.name),
        fol::Sort::Integer => fol::GeneralTerm::IntegerTerm(fol::IntegerTerm::Variable(z.name)),
        fol::Sort::Symbol => unreachable!("tau* should not produce variables of the Symbol sort"),
    };

    // I = J * Q + R
    let qvar = choose_fresh_variable_names(&taken_vars, "Q", 1)
        .pop()
        .unwrap();
    let rvar = choose_fresh_variable_names(&taken_vars, "R", 1)
        .pop()
        .unwrap();
    let iequals = fol::Formula::AtomicFormula(fol::AtomicFormula::Comparison(fol::Comparison {
        term: fol::GeneralTerm::IntegerTerm(fol::IntegerTerm::Variable(i.clone())),
        guards: vec![fol::Guard {
            relation: fol::Relation::Equal,
            term: fol::GeneralTerm::IntegerTerm(fol::IntegerTerm::BinaryOperation {
                op: fol::BinaryOperator::Add,
                lhs: fol::IntegerTerm::BinaryOperation {
                    op: fol::BinaryOperator::Multiply,
                    lhs: fol::IntegerTerm::Variable(j.clone()).into(),
                    rhs: fol::IntegerTerm::Variable(qvar.clone()).into(),
                }
                .into(),
                rhs: fol::IntegerTerm::Variable(rvar.clone()).into(),
            }),
        }],
    }));

    // J != 0 & R >= 0 & R < Q
    let conditions = fol::Formula::BinaryFormula {
        connective: fol::BinaryConnective::Conjunction,
        lhs: fol::Formula::BinaryFormula {
            connective: fol::BinaryConnective::Conjunction,
            lhs: fol::Formula::AtomicFormula(fol::AtomicFormula::Comparison(fol::Comparison {
                term: fol::GeneralTerm::IntegerTerm(fol::IntegerTerm::Variable(j.clone())),
                guards: vec![fol::Guard {
                    relation: fol::Relation::NotEqual,
                    term: fol::GeneralTerm::IntegerTerm(fol::IntegerTerm::Numeral(0)),
                }],
            }))
            .into(),
            rhs: fol::Formula::AtomicFormula(fol::AtomicFormula::Comparison(fol::Comparison {
                term: fol::GeneralTerm::IntegerTerm(fol::IntegerTerm::Variable(rvar.clone())),
                guards: vec![fol::Guard {
                    relation: fol::Relation::GreaterEqual,
                    term: fol::GeneralTerm::IntegerTerm(fol::IntegerTerm::Numeral(0)),
                }],
            }))
            .into(),
        }
        .into(),
        rhs: fol::Formula::AtomicFormula(fol::AtomicFormula::Comparison(fol::Comparison {
            term: fol::GeneralTerm::IntegerTerm(fol::IntegerTerm::Variable(rvar.clone())),
            guards: vec![fol::Guard {
                relation: fol::Relation::Less,
                term: fol::GeneralTerm::IntegerTerm(fol::IntegerTerm::Variable(j.clone())),
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
                    term: fol::GeneralTerm::IntegerTerm(fol::IntegerTerm::Variable(qvar.clone())),
                }],
            }))
        }
        asp::BinaryOperator::Modulo => {
            fol::Formula::AtomicFormula(fol::AtomicFormula::Comparison(fol::Comparison {
                term: z_var_term,
                guards: vec![fol::Guard {
                    relation: fol::Relation::Equal,
                    term: fol::GeneralTerm::IntegerTerm(fol::IntegerTerm::Variable(rvar.clone())),
                }],
            }))
        }
        _ => unreachable!("division and modulo are the only supported partial functions"),
    };

    fol::Formula::QuantifiedFormula {
        quantification: fol::Quantification {
            quantifier: fol::Quantifier::Exists,
            variables: vec![
                fol::Variable {
                    name: i,
                    sort: fol::Sort::Integer,
                },
                fol::Variable {
                    name: j,
                    sort: fol::Sort::Integer,
                },
                fol::Variable {
                    name: qvar,
                    sort: fol::Sort::Integer,
                },
                fol::Variable {
                    name: rvar,
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
// exists I J K (val_t1(I) & val_t2(J) & I <= K <= J & Z = K)
fn construct_interval_formula(
    valti: fol::Formula,
    valtj: fol::Formula,
    i_var: fol::Variable,
    j_var: fol::Variable,
    k_var: fol::Variable,
    z: fol::Variable,
) -> fol::Formula {
    let z_var_term = match z.sort {
        fol::Sort::General => fol::GeneralTerm::Variable(z.name),
        fol::Sort::Integer => fol::GeneralTerm::IntegerTerm(fol::IntegerTerm::Variable(z.name)),
        fol::Sort::Symbol => unreachable!("tau* should not produce variables of the Symbol sort"),
    };

    // I <= K <= J
    let range = fol::Formula::AtomicFormula(fol::AtomicFormula::Comparison(fol::Comparison {
        term: fol::GeneralTerm::IntegerTerm(fol::IntegerTerm::Variable(i_var.name.clone())),
        guards: vec![
            fol::Guard {
                relation: fol::Relation::LessEqual,
                term: fol::GeneralTerm::IntegerTerm(fol::IntegerTerm::Variable(k_var.name.clone())),
            },
            fol::Guard {
                relation: fol::Relation::LessEqual,
                term: fol::GeneralTerm::IntegerTerm(fol::IntegerTerm::Variable(j_var.name.clone())),
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
                term: fol::GeneralTerm::IntegerTerm(fol::IntegerTerm::Variable(k_var.name.clone())),
            }],
        }))
        .into(),
    };

    fol::Formula::QuantifiedFormula {
        quantification: fol::Quantification {
            quantifier: fol::Quantifier::Exists,
            variables: vec![i_var, j_var, k_var],
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
fn val(t: asp::Term, z: fol::Variable) -> fol::Formula {
    let mut taken_vars = IndexSet::<fol::Variable>::new();
    for var in t.variables().iter() {
        taken_vars.insert(fol::Variable {
            name: var.to_string(),
            sort: fol::Sort::General,
        });
    }
    taken_vars.insert(z.clone());

    let mut fresh_ivar = choose_fresh_variable_names(&taken_vars, "I", 1);
    let mut fresh_jvar = choose_fresh_variable_names(&taken_vars, "J", 1);
    let mut fresh_kvar = choose_fresh_variable_names(&taken_vars, "K", 1);

    // Fresh integer variables
    let var1 = fol::Variable {
        name: fresh_ivar.pop().unwrap(),
        sort: fol::Sort::Integer,
    };
    let var2 = fol::Variable {
        name: fresh_jvar.pop().unwrap(),
        sort: fol::Sort::Integer,
    };
    let var3 = fol::Variable {
        name: fresh_kvar.pop().unwrap(),
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
                        var1,
                        var2,
                        z,
                    )
                }
            }
        }
        asp::Term::BinaryOperation { op, lhs, rhs } => {
            let valti = val(*lhs, var1.clone()); // val_t1(I)
            let valtj = val(*rhs, var2.clone()); // val_t2(J)
            match op {
                asp::BinaryOperator::Add => construct_total_function_formula(
                    valti,
                    valtj,
                    asp::BinaryOperator::Add,
                    var1,
                    var2,
                    z,
                ),
                asp::BinaryOperator::Subtract => construct_total_function_formula(
                    valti,
                    valtj,
                    asp::BinaryOperator::Subtract,
                    var1,
                    var2,
                    z,
                ),
                asp::BinaryOperator::Multiply => construct_total_function_formula(
                    valti,
                    valtj,
                    asp::BinaryOperator::Multiply,
                    var1,
                    var2,
                    z,
                ),
                asp::BinaryOperator::Divide => construct_partial_function_formula(
                    valti,
                    valtj,
                    asp::BinaryOperator::Divide,
                    var1,
                    var2,
                    z,
                ),
                asp::BinaryOperator::Modulo => construct_partial_function_formula(
                    valti,
                    valtj,
                    asp::BinaryOperator::Modulo,
                    var1,
                    var2,
                    z,
                ),
                asp::BinaryOperator::Interval => {
                    construct_interval_formula(valti, valtj, var1, var2, var3, z)
                }
            }
        }
    }
}

// val_t1(Z1) & val_t2(Z2) & ... & val_tn(Zn)
fn valtz(mut terms: Vec<asp::Term>, mut variables: Vec<fol::Variable>) -> fol::Formula {
    fol::Formula::conjoin(
        terms
            .drain(..)
            .zip(variables.drain(..))
            .map(|(t, v)| val(t, v)),
    )
}

// Translate a first-order body literal
fn tau_b_first_order_literal(l: asp::Literal, taken_vars: IndexSet<fol::Variable>) -> fol::Formula {
    let atom = l.atom;
    let terms = atom.terms;
    let arity = terms.len();
    let varnames = choose_fresh_variable_names(&taken_vars, "Z", arity);

    // Compute val_t1(Z1) & val_t2(Z2) & ... & val_tk(Zk)
    let mut var_terms: Vec<fol::GeneralTerm> = Vec::with_capacity(arity);
    let mut var_vars: Vec<fol::Variable> = Vec::with_capacity(arity);
    let mut valtz_vec: Vec<fol::Formula> = Vec::with_capacity(arity);
    for (i, t) in terms.iter().enumerate() {
        let var = fol::Variable {
            sort: fol::Sort::General,
            name: varnames[i].clone(),
        };
        valtz_vec.push(val(t.clone(), var.clone()));
        var_terms.push(fol::GeneralTerm::Variable(varnames[i].clone()));
        var_vars.push(var);
    }
    let valtz = fol::Formula::conjoin(valtz_vec);

    // Compute p(Z1, Z2, ..., Zk)
    let p_zk = fol::Formula::AtomicFormula(fol::AtomicFormula::Atom(fol::Atom {
        predicate_symbol: atom.predicate_symbol,
        terms: var_terms,
    }));

    // Compute tau^b(B)
    match l.sign {
        asp::Sign::NoSign => fol::Formula::QuantifiedFormula {
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
        asp::Sign::Negation => fol::Formula::QuantifiedFormula {
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
        asp::Sign::DoubleNegation => fol::Formula::QuantifiedFormula {
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
}

// Translate a propositional body literal
fn tau_b_propositional_literal(l: asp::Literal) -> fol::Formula {
    let atom = l.atom;
    match l.sign {
        asp::Sign::NoSign => fol::Formula::AtomicFormula(fol::AtomicFormula::Atom(fol::Atom {
            predicate_symbol: atom.predicate_symbol,

            terms: vec![],
        })),
        asp::Sign::Negation => fol::Formula::UnaryFormula {
            connective: fol::UnaryConnective::Negation,
            formula: fol::Formula::AtomicFormula(fol::AtomicFormula::Atom(fol::Atom {
                predicate_symbol: atom.predicate_symbol,
                terms: vec![],
            }))
            .into(),
        },
        asp::Sign::DoubleNegation => fol::Formula::UnaryFormula {
            connective: fol::UnaryConnective::Negation,
            formula: fol::Formula::UnaryFormula {
                connective: fol::UnaryConnective::Negation,
                formula: fol::Formula::AtomicFormula(fol::AtomicFormula::Atom(fol::Atom {
                    predicate_symbol: atom.predicate_symbol,
                    terms: vec![],
                }))
                .into(),
            }
            .into(),
        },
    }
}

// Translate a body comparison
fn tau_b_comparison(c: asp::Comparison, taken_vars: IndexSet<fol::Variable>) -> fol::Formula {
    let varnames = choose_fresh_variable_names(&taken_vars, "Z", 2);

    // Compute val_t1(Z1) & val_t2(Z2)
    let term_z1 = fol::GeneralTerm::Variable(varnames[0].clone());
    let term_z2 = fol::GeneralTerm::Variable(varnames[1].clone());
    let var_z1 = fol::Variable {
        sort: fol::Sort::General,
        name: varnames[0].clone(),
    };
    let var_z2 = fol::Variable {
        sort: fol::Sort::General,
        name: varnames[1].clone(),
    };
    let valtz = fol::Formula::conjoin(vec![val(c.lhs, var_z1.clone()), val(c.rhs, var_z2.clone())]);

    // Compute Z1 rel Z2
    let z1_rel_z2 = fol::Formula::AtomicFormula(fol::AtomicFormula::Comparison(fol::Comparison {
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

// Translate a body literal or comparison
fn tau_b(f: asp::AtomicFormula) -> fol::Formula {
    let mut taken_vars = IndexSet::<fol::Variable>::new();
    for var in f.variables().iter() {
        taken_vars.insert(fol::Variable {
            name: var.to_string(),
            sort: fol::Sort::General,
        });
    }
    match f {
        asp::AtomicFormula::Literal(l) => {
            let arity = l.atom.terms.len();
            if arity > 0 {
                tau_b_first_order_literal(l, taken_vars)
            } else {
                tau_b_propositional_literal(l)
            }
        }
        asp::AtomicFormula::Comparison(c) => tau_b_comparison(c, taken_vars),
    }
}

// Translate a rule body
fn tau_body(b: asp::Body) -> fol::Formula {
    let mut formulas = Vec::<fol::Formula>::new();
    for f in b.formulas.iter() {
        formulas.push(tau_b(f.clone()));
    }
    fol::Formula::conjoin(formulas)
}

// Handles the case when we have a rule with a first-order atom or choice atom in the head
fn tau_star_fo_head_rule(r: &asp::Rule, globals: &[String]) -> fol::Formula {
    let head_symbol = r.head.predicate().unwrap();
    let fol_head_predicate = fol::Predicate {
        symbol: head_symbol.symbol,
        arity: head_symbol.arity,
    };
    let head_arity = r.head.arity(); // n
    let fvars = &globals[0..head_arity]; // V, |V| = n
    let mut gvars = Vec::<fol::Variable>::new(); // G
    for var in r.variables().iter() {
        gvars.push(fol::Variable {
            sort: fol::Sort::General,
            name: var.to_string(),
        });
    }

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
        asp::Head::Basic(_) => core_lhs, // val_t(V) & tau^B(Body)
        asp::Head::Choice(_) => fol::Formula::BinaryFormula {
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
    let imp = fol::Formula::BinaryFormula {
        connective: fol::BinaryConnective::Implication,
        lhs: new_body.into(),
        rhs: new_head.into(),
    }; // val_t(V) & tau^B(Body) -> p(V) OR val_t(V) & tau^B(Body) & ~~p(V) -> p(V)
    for var in fvars.iter() {
        gvars.push(fol::Variable {
            sort: fol::Sort::General,
            name: var.to_string(),
        });
    }
    gvars.sort(); // TODO
    fol::Formula::QuantifiedFormula {
        quantification: fol::Quantification {
            quantifier: fol::Quantifier::Forall,
            variables: gvars,
        },
        formula: imp.into(),
    } // forall G V ( val_t(V) & tau^B(Body) -> p(V) ) OR forall G V ( val_t(V) & tau^B(Body) -> p(V) )
}

// Handles the case when we have a rule with a propositional atom or choice atom in the head
fn tau_star_prop_head_rule(r: &asp::Rule) -> fol::Formula {
    let head_symbol = r.head.predicate().unwrap();
    let fol_head_predicate = fol::Predicate {
        symbol: head_symbol.symbol,
        arity: head_symbol.arity,
    };
    let mut gvars = Vec::<fol::Variable>::new(); // G
    for var in r.variables().iter() {
        gvars.push(fol::Variable {
            sort: fol::Sort::General,
            name: var.to_string(),
        });
    }
    let new_head = fol::Formula::AtomicFormula(fol::AtomicFormula::Atom(fol::Atom {
        predicate_symbol: fol_head_predicate.symbol,
        terms: vec![],
    }));
    let core_lhs = tau_body(r.body.clone());
    let new_body = match &r.head {
        asp::Head::Basic(_) => {
            // tau^B(Body)
            core_lhs
        }
        asp::Head::Choice(_) => {
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
        asp::Head::Falsity => {
            unreachable!("a constraint head is not permitted in this formula constructor")
        }
    };

    let imp = fol::Formula::BinaryFormula {
        // tau^B(Body) -> p OR tau^B(Body) & ~~p -> p
        connective: fol::BinaryConnective::Implication,
        lhs: new_body.into(),
        rhs: new_head.into(),
    };
    gvars.sort(); // TODO
    if !gvars.is_empty() {
        // forall G ( tau^B(Body) -> p ) OR forall G ( tau^B(Body) & ~~p -> p )
        fol::Formula::QuantifiedFormula {
            quantification: fol::Quantification {
                quantifier: fol::Quantifier::Forall,
                variables: gvars,
            },
            formula: imp.into(),
        }
    } else {
        imp // tau^B(Body) -> p  OR tau^B(Body) & ~~p -> p
    }
}

// Handles the case when we have a rule with an empty head
fn tau_star_constraint_rule(r: &asp::Rule) -> fol::Formula {
    let mut gvars = Vec::<fol::Variable>::new();
    for var in r.variables().iter() {
        gvars.push(fol::Variable {
            sort: fol::Sort::General,
            name: var.to_string(),
        });
    }
    let imp = fol::Formula::BinaryFormula {
        connective: fol::BinaryConnective::Implication,
        lhs: tau_body(r.body.clone()).into(),
        rhs: fol::Formula::AtomicFormula(fol::AtomicFormula::Falsity).into(),
    }; // tau^B(Body) -> \bot
    gvars.sort(); // TODO
    if !gvars.is_empty() {
        fol::Formula::QuantifiedFormula {
            quantification: fol::Quantification {
                quantifier: fol::Quantifier::Forall,
                variables: gvars,
            },
            formula: imp.into(),
        } // forall G ( tau^B(Body) -> \bot )
    } else {
        imp
    } // tau^B(Body) -> \bot
}

// Translate a rule using a pre-defined list of global variables
fn tau_star_rule(r: &asp::Rule, globals: &[String]) -> fol::Formula {
    match r.head.predicate() {
        Some(_) => {
            if r.head.arity() > 0 {
                // First-order head
                tau_star_fo_head_rule(r, globals)
            } else {
                // Propositional head
                tau_star_prop_head_rule(r)
            }
        }
        None => tau_star_constraint_rule(r),
    }
}

// For each rule, produce a formula: forall G V ( val_t(V) & tau_body(Body) -> p(V) )
// Where G is all variables from the original rule
// and V is the set of fresh variables replacing t within p
pub fn tau_star(p: asp::Program) -> fol::Theory {
    let globals = choose_fresh_global_variables(&p);
    let mut formulas: Vec<fol::Formula> = vec![]; // { forall G V ( val_t(V) & tau^B(Body) -> p(V) ), ... }
    for r in p.rules.iter() {
        formulas.push(tau_star_rule(r, &globals));
    }
    fol::Theory { formulas }
}

#[cfg(test)]
mod tests {
    use super::{tau_b, tau_star, val};

    #[test]
    fn test_val() {
        for (term, var, target) in [
            ("X + 1", "Z1", "exists I$i J$i (Z1$g = I$i + J$i and I$i = X and J$i = 1)"),
            ("3 - 5", "Z1", "exists I$i J$i (Z1$g = I$i - J$i and I$i = 3 and J$i = 5)"),
            ("Xanadu/Yak", "Z1", "exists I$i J$i Q$i R$i (I$i = J$i * Q$i + R$i and (I$i = Xanadu and J$i = Yak) and (J$i != 0 and R$i >= 0 and R$i < J$i) and Z1$g = Q$i)"),
            ("X \\ 3", "Z1", "exists I$i J$i Q$i R$i (I$i = J$i * Q$i + R$i and (I$i = X and J$i = 3) and (J$i != 0 and R$i >= 0 and R$i < J$i) and Z1$g = R$i)"),
            ("X..Y", "Z", "exists I$i J$i K$i (I$i = X and J$i = Y and Z$g = K$i and I$i <= K$i <= J$i)"),
            ("X+1..Y", "Z1", "exists I$i J$i K$i ((exists I1$i J$i (I$i = I1$i + J$i and I1$i = X and J$i = 1)) and J$i = Y and Z1 = K$i and I$i <= K$i <= J$i)"),
        ] {
            let left = val(term.parse().unwrap(), var.parse().unwrap());
            let right = target.parse().unwrap();

            assert!(
                left == right,
                "assertion `left == right` failed:\n left:\n{left}\n right:\n{right}"
            );
        }
    }

    #[test]
    fn test_tau_b() {
        for (src, target) in [
            ("p(t)", "exists Z (Z = t and p(Z))"),
            ("not p(t)", "exists Z (Z = t and not p(Z))"),
            ("X < 1..5", "exists Z Z1 (Z = X and exists I$i J$i K$i (I$i = 1 and J$i = 5 and Z1 = K$i and I$i <= K$i <= J$i) and Z < Z1)"),
            ("not not p(t)", "exists Z (Z = t and not not p(Z))"),
            ("not not x", "not not x"),
            ("not p(X,5)", "exists Z Z1 (Z = X and Z1 = 5 and not p(Z,Z1))"),
            ("not p(X,0-5)", "exists Z Z1 (Z = X and exists I$i J$i (Z1 = I$i - J$i and I$i = 0 and J$i = 5) and not p(Z,Z1))"),
            ("p(X,-1..5)", "exists Z Z1 (Z = X and exists I$i J$i K$i (I$i = -1 and J$i = 5 and Z1 = K$i and I$i <= K$i <= J$i) and p(Z,Z1))"),
            ("p(X,-(1..5))", "exists Z Z1 (Z = X and exists I$i J$i (Z1 = I$i - J$i and I$i = 0 and exists I$i J1$i K$i (I$i = 1 and J1$i = 5  and J$i = K$i and I$i <= K$i <= J1$i)) and p(Z,Z1))")
        ] {
            let left = tau_b(src.parse().unwrap());
            let right = target.parse().unwrap();

            assert!(
                left == right,
                "assertion `left == right` failed:\n left:\n{left}\n right:\n{right}"
            );
        }
    }

    #[test]
    fn test_tau_star() {
        for (src, target) in [
            ("a:- b. a :- c.", "b -> a. c -> a."),
            ("p(a). p(b). q(X, Y) :- p(X), p(Y).", "forall V1 (V1 = a and #true -> p(V1)). forall V1 (V1 = b and #true -> p(V1)). forall V1 V2 X Y (V1 = X and V2 = Y and (exists Z (Z = X and p(Z)) and exists Z (Z = Y and p(Z))) -> q(V1,V2))."),
            ("p.", "#true -> p."),
            ("q :- not p.", "not p -> q."),
            ("{q(X)} :- p(X).", "forall V1 X (V1 = X and exists Z (Z = X and p(Z)) and not not q(V1) -> q(V1))."),
            ("{q(V)} :- p(V).", "forall V V1 (V1 = V and exists Z (Z = V and p(Z)) and not not q(V1) -> q(V1))."),
            ("{q(V+1)} :- p(V), not q(X).", "forall V V1 X (exists I$i J$i (V1 = I$i + J$i and I$i = V and J$i = 1) and (exists Z (Z = V and p(Z)) and exists Z (Z = X and not q(Z))) and not not q(V1) -> q(V1))."),
            (":- p(X,3), not q(X,a).", "forall X (exists Z Z1 (Z = X and Z1 = 3 and p(Z,Z1)) and exists Z Z1 (Z = X and Z1 = a and not q(Z,Z1)) -> #false)."),
            (":- p.", "p -> #false."),
            ("{p} :- q.", "q and not not p -> p."),
            ("{p}.", "#true and not not p -> p."),
            ("{p(5)}.", "forall V1 (V1 = 5 and #true and not not p(V1) -> p(V1))."),
            ("p. q.", "#true -> p. #true -> q."),
            ("{ra(X,a)} :- ta(X). ra(5,a).", "forall V1 V2 X (V1 = X and V2 = a and exists Z (Z = X and ta(Z)) and not not ra(V1, V2) -> ra(V1, V2)). forall V1 V2 (V1 = 5 and V2 = a and #true -> ra(V1, V2))."),
            ("p(X/2) :- X=4.", "forall V1 X (exists I$i J$i Q$i R$i (I$i = J$i * Q$i + R$i and (I$i = X and J$i = 2) and (J$i != 0 and R$i >= 0 and R$i < J$i) and V1 = Q$i) and exists Z Z1 (Z = X and Z1 = 4 and Z = Z1) -> p(V1))."),
        ] {
            let left = tau_star(src.parse().unwrap());
            let right = target.parse().unwrap();

            assert!(
                left == right,
                "assertion `left == right` failed:\n left:\n{left}\n right:\n{right}"
            );
        }
    }
}
