use {
    crate::{
        command_line::arguments::Dialect,
        convenience::{apply::Apply, compose::Compose, variable_selection::VariableSelection},
        simplifying::fol::sigma_0::intuitionistic::{
            remove_conjunctive_identities, remove_empty_quantifications, remove_orphaned_variables,
        },
        syntax_tree::{
            asp::mini_gringo::{self as asp, Program},
            fol::sigma_0::{
                self as fol, Atom, AtomicFormula, BinaryConnective, BinaryOperator, Comparison,
                Formula, Function, GeneralTerm, Guard, IntegerTerm, Quantification, Quantifier,
                Relation, Sort, SymbolicTerm, Theory, UnaryConnective, UnaryOperator, Variable,
            },
        },
    },
    indexmap::{IndexMap, IndexSet},
};

pub const PREPROCESS: &[fn(Formula) -> Formula] = &[
    remove_conjunctive_identities,
    remove_orphaned_variables,
    remove_empty_quantifications,
];

/// Choose fresh variants of `Vn` by incrementing `n`
pub(crate) fn choose_fresh_global_variables(program: &Program) -> Vec<String> {
    let max_arity = program.max_arity();
    program.choose_fresh_variables("V", max_arity)
}

fn choose_fresh_ijk(taken_variables: IndexSet<Variable>) -> IndexMap<String, Variable> {
    let mut fresh_int_vars = IndexMap::new();

    fresh_int_vars.insert(
        "I".to_string(),
        Variable {
            name: taken_variables.choose_fresh_variable("I"),
            sort: Sort::Integer,
        },
    );
    fresh_int_vars.insert(
        "J".to_string(),
        Variable {
            name: taken_variables.choose_fresh_variable("J"),
            sort: Sort::Integer,
        },
    );
    fresh_int_vars.insert(
        "K".to_string(),
        Variable {
            name: taken_variables.choose_fresh_variable("K"),
            sort: Sort::Integer,
        },
    );

    fresh_int_vars
}

// Z = t
fn construct_equality_formula(term: asp::Term, z: Variable) -> Formula {
    let rhs = match term {
        asp::Term::BasicSymbol(t) => match t {
            asp::BasicSymbol::Infimum => GeneralTerm::Infimum,
            asp::BasicSymbol::Supremum => GeneralTerm::Supremum,
            asp::BasicSymbol::Numeral(i) => GeneralTerm::IntegerTerm(IntegerTerm::Numeral(i)),
            asp::BasicSymbol::Symbol(s) => GeneralTerm::SymbolicTerm(SymbolicTerm::Symbol(s)),
        },
        asp::Term::Variable(v) => GeneralTerm::Variable(v.0),
        _ => unreachable!(
            "equality should be between two variables or a variable and a precomputed term"
        ),
    };

    Formula::AtomicFormula(AtomicFormula::Comparison(Comparison {
        term: z.into(),
        guards: vec![Guard {
            relation: Relation::Equal,
            term: rhs,
        }],
    }))
}

// op: +,-,*
// exists I J (Z = I op J & val_t1(I) & val_t2(J))
fn construct_total_function_formula(
    valti: Formula,
    valtj: Formula,
    binop: asp::BinaryOperator,
    i_var: Variable,
    j_var: Variable,
    z: Variable,
) -> Formula {
    // Z = I binop J
    let zequals = Formula::AtomicFormula(AtomicFormula::Comparison(Comparison {
        term: z.into(),
        guards: vec![Guard {
            relation: Relation::Equal,
            term: GeneralTerm::IntegerTerm(IntegerTerm::BinaryOperation {
                op: match binop {
                    asp::BinaryOperator::Add => BinaryOperator::Add,
                    asp::BinaryOperator::Subtract => BinaryOperator::Subtract,
                    asp::BinaryOperator::Multiply => BinaryOperator::Multiply,
                    _ => unreachable!(
                        "addition, subtraction and multiplication are the only supported total functions"
                    ),
                },
                lhs: IntegerTerm::Variable(i_var.name.clone()).into(),
                rhs: IntegerTerm::Variable(j_var.name.clone()).into(),
            }),
        }],
    }));
    Formula::QuantifiedFormula {
        quantification: Quantification {
            quantifier: Quantifier::Exists,
            variables: vec![i_var, j_var],
        },
        formula: Formula::BinaryFormula {
            connective: BinaryConnective::Conjunction,
            lhs: Formula::BinaryFormula {
                connective: BinaryConnective::Conjunction,
                lhs: zequals.into(),
                rhs: valti.into(),
            }
            .into(),
            rhs: valtj.into(),
        }
        .into(),
    }
}

// t1..t2
// exists I J K (val_t1(I) & val_t2(J) & I <= K <= J & Z = K)
fn construct_interval_formula(
    valti: Formula,
    valtj: Formula,
    i_var: Variable,
    j_var: Variable,
    k_var: Variable,
    z: Variable,
) -> Formula {
    // I <= K <= J
    let range = Formula::AtomicFormula(AtomicFormula::Comparison(Comparison {
        term: GeneralTerm::IntegerTerm(IntegerTerm::Variable(i_var.name.clone())),
        guards: vec![
            Guard {
                relation: Relation::LessEqual,
                term: GeneralTerm::IntegerTerm(IntegerTerm::Variable(k_var.name.clone())),
            },
            Guard {
                relation: Relation::LessEqual,
                term: GeneralTerm::IntegerTerm(IntegerTerm::Variable(j_var.name.clone())),
            },
        ],
    }));

    // val_t1(I) & val_t2(J) & Z = k
    let subformula = Formula::BinaryFormula {
        connective: BinaryConnective::Conjunction,
        lhs: Formula::BinaryFormula {
            connective: BinaryConnective::Conjunction,
            lhs: valti.into(),
            rhs: valtj.into(),
        }
        .into(),
        rhs: Formula::AtomicFormula(AtomicFormula::Comparison(Comparison {
            term: z.into(),
            guards: vec![Guard {
                relation: Relation::Equal,
                term: GeneralTerm::IntegerTerm(IntegerTerm::Variable(k_var.name.clone())),
            }],
        }))
        .into(),
    };

    Formula::QuantifiedFormula {
        quantification: Quantification {
            quantifier: Quantifier::Exists,
            variables: vec![i_var, j_var, k_var],
        },
        formula: Formula::BinaryFormula {
            connective: BinaryConnective::Conjunction,
            lhs: subformula.into(),
            rhs: range.into(),
        }
        .into(),
    }
}

// |t|
// exists I$ (Z = I$ & val_t(I$))
fn construct_absolute_value_formula(valti: Formula, i_var: Variable, z: Variable) -> Formula {
    // Z = |I|
    let zequals = Formula::AtomicFormula(AtomicFormula::Comparison(Comparison {
        term: z.into(),
        guards: vec![Guard {
            relation: Relation::Equal,
            term: GeneralTerm::IntegerTerm(IntegerTerm::UnaryOperation {
                op: UnaryOperator::AbsoluteValue,
                arg: IntegerTerm::Variable(i_var.name.clone()).into(),
            }),
        }],
    }));

    Formula::QuantifiedFormula {
        quantification: Quantification {
            quantifier: Quantifier::Exists,
            variables: vec![i_var],
        },
        formula: Formula::BinaryFormula {
            connective: BinaryConnective::Conjunction,
            lhs: zequals.into(),
            rhs: valti.into(),
        }
        .into(),
    }
}

// I,J,K must be integer variables
// f1: K * |J| <= |I| < (K+1) * |J|
fn division_helper_f1(i: Variable, j: Variable, k: Variable) -> Formula {
    // K * |J|
    let term1 = GeneralTerm::IntegerTerm(IntegerTerm::BinaryOperation {
        op: BinaryOperator::Multiply,
        lhs: IntegerTerm::Variable(k.name.clone()).into(),
        rhs: IntegerTerm::UnaryOperation {
            op: UnaryOperator::AbsoluteValue,
            arg: IntegerTerm::Variable(j.name.clone()).into(),
        }
        .into(),
    });

    // |I|
    let term2 = GeneralTerm::IntegerTerm(IntegerTerm::UnaryOperation {
        op: UnaryOperator::AbsoluteValue,
        arg: IntegerTerm::Variable(i.name.clone()).into(),
    });

    // (K+1) * |J|
    let term3 = GeneralTerm::IntegerTerm(IntegerTerm::BinaryOperation {
        op: BinaryOperator::Multiply,
        lhs: IntegerTerm::BinaryOperation {
            op: BinaryOperator::Add,
            lhs: IntegerTerm::Variable(k.name.clone()).into(),
            rhs: IntegerTerm::Numeral(1).into(),
        }
        .into(),
        rhs: IntegerTerm::UnaryOperation {
            op: UnaryOperator::AbsoluteValue,
            arg: IntegerTerm::Variable(j.name.clone()).into(),
        }
        .into(),
    });

    Formula::AtomicFormula(AtomicFormula::Comparison(Comparison {
        term: term1,
        guards: vec![
            Guard {
                relation: Relation::LessEqual,
                term: term2,
            },
            Guard {
                relation: Relation::Less,
                term: term3,
            },
        ],
    }))
}

// f2: (I * J >= 0 & Z = K) v (I * J < 0 & Z = -K)
fn division_helper_f2(
    i: Variable, // Must be an integer variable
    j: Variable, // Must be an integer variable
    k: Variable, // Must be an integer variable
    z: Variable, // Must be a general variable
) -> Formula {
    // I * J
    let i_times_j = GeneralTerm::IntegerTerm(IntegerTerm::BinaryOperation {
        op: BinaryOperator::Multiply,
        lhs: IntegerTerm::Variable(i.name.clone()).into(),
        rhs: IntegerTerm::Variable(j.name.clone()).into(),
    });

    // I * J >= 0
    let ij_geq_zero = Formula::AtomicFormula(AtomicFormula::Comparison(Comparison {
        term: i_times_j.clone(),
        guards: vec![Guard {
            relation: Relation::GreaterEqual,
            term: GeneralTerm::IntegerTerm(IntegerTerm::Numeral(0)),
        }],
    }));

    // Z = K
    let z_equals_k = Formula::AtomicFormula(AtomicFormula::Comparison(Comparison {
        term: z.clone().into(),
        guards: vec![Guard {
            relation: Relation::Equal,
            term: GeneralTerm::IntegerTerm(IntegerTerm::Variable(k.name.clone())),
        }],
    }));

    // I * J < 0
    let ij_less_zero = Formula::AtomicFormula(AtomicFormula::Comparison(Comparison {
        term: i_times_j,
        guards: vec![Guard {
            relation: Relation::Less,
            term: GeneralTerm::IntegerTerm(IntegerTerm::Numeral(0)),
        }],
    }));

    // Z = -K
    let z_equals_neg_k = Formula::AtomicFormula(AtomicFormula::Comparison(Comparison {
        term: z.into(),
        guards: vec![Guard {
            relation: Relation::Equal,
            term: GeneralTerm::IntegerTerm(IntegerTerm::UnaryOperation {
                op: UnaryOperator::Negative,
                arg: IntegerTerm::Variable(k.name).into(),
            }),
        }],
    }));

    Formula::BinaryFormula {
        connective: BinaryConnective::Disjunction,
        lhs: Formula::BinaryFormula {
            connective: BinaryConnective::Conjunction,
            lhs: ij_geq_zero.into(),
            rhs: z_equals_k.into(),
        }
        .into(),
        rhs: Formula::BinaryFormula {
            connective: BinaryConnective::Conjunction,
            lhs: ij_less_zero.into(),
            rhs: z_equals_neg_k.into(),
        }
        .into(),
    }
}

// Arguments must be integer variables
// f3: (I * J >= 0 & Z = I - K * J) v (I * J < 0 & Z = I + K * J)
fn division_helper_f3(i: Variable, j: Variable, k: Variable, z: Variable) -> Formula {
    // I * J
    let i_times_j = GeneralTerm::IntegerTerm(IntegerTerm::BinaryOperation {
        op: BinaryOperator::Multiply,
        lhs: IntegerTerm::Variable(i.name.clone()).into(),
        rhs: IntegerTerm::Variable(j.name.clone()).into(),
    });

    // I * J >= 0
    let ij_geq_zero = Formula::AtomicFormula(AtomicFormula::Comparison(Comparison {
        term: i_times_j.clone(),
        guards: vec![Guard {
            relation: Relation::GreaterEqual,
            term: GeneralTerm::IntegerTerm(IntegerTerm::Numeral(0)),
        }],
    }));

    // I * J < 0
    let ij_less_zero = Formula::AtomicFormula(AtomicFormula::Comparison(Comparison {
        term: i_times_j,
        guards: vec![Guard {
            relation: Relation::Less,
            term: GeneralTerm::IntegerTerm(IntegerTerm::Numeral(0)),
        }],
    }));

    // K * J
    let k_times_j = IntegerTerm::BinaryOperation {
        op: BinaryOperator::Multiply,
        lhs: IntegerTerm::Variable(k.name.clone()).into(),
        rhs: IntegerTerm::Variable(j.name.clone()).into(),
    };

    // Z = I - K * J
    let z_equals_i_minus = Formula::AtomicFormula(AtomicFormula::Comparison(Comparison {
        term: z.clone().into(),
        guards: vec![Guard {
            relation: Relation::Equal,
            term: GeneralTerm::IntegerTerm(IntegerTerm::BinaryOperation {
                op: BinaryOperator::Subtract,
                lhs: IntegerTerm::Variable(i.name.clone()).into(),
                rhs: k_times_j.clone().into(),
            }),
        }],
    }));

    // Z = I + K * J
    let z_equals_i_plus = Formula::AtomicFormula(AtomicFormula::Comparison(Comparison {
        term: z.into(),
        guards: vec![Guard {
            relation: Relation::Equal,
            term: GeneralTerm::IntegerTerm(IntegerTerm::BinaryOperation {
                op: BinaryOperator::Add,
                lhs: IntegerTerm::Variable(i.name.clone()).into(),
                rhs: k_times_j.into(),
            }),
        }],
    }));

    Formula::BinaryFormula {
        connective: BinaryConnective::Disjunction,
        lhs: Formula::BinaryFormula {
            connective: BinaryConnective::Conjunction,
            lhs: ij_geq_zero.into(),
            rhs: z_equals_i_minus.into(),
        }
        .into(),
        rhs: Formula::BinaryFormula {
            connective: BinaryConnective::Conjunction,
            lhs: ij_less_zero.into(),
            rhs: z_equals_i_plus.into(),
        }
        .into(),
    }
}

// Abstract Gringo compliant integer division and modulo.
// Follows Locally Tight Programs (2023), Conditional literals & Arithmetic (2025)
// Division: exists I J K (val_t1(I) & val_t2(J) & F1(IJK) & F2(IJKZ))
// Modulo:   exists I J K (val_t1(I) & val_t2(J) & F1(IJK) & F3(IJKZ))
fn construct_gfive_partial_function_formula(
    valti: Formula,
    valtj: Formula,
    binop: asp::BinaryOperator,
    i: Variable,
    j: Variable,
    k: Variable,
    z: Variable,
) -> Formula {
    assert_eq!(i.sort, Sort::Integer);
    assert_eq!(j.sort, Sort::Integer);
    assert_eq!(k.sort, Sort::Integer);
    //assert_eq!(z.sort, Sort::General);

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

// I = J * Q + R & val_t1(I) & val_t2(J) & J != 0 & R >= 0 & R < J
fn division_helper_f4(
    valti: Formula,
    valtj: Formula,
    i: Variable,
    j: Variable,
    q: Variable,
    r: Variable,
) -> Formula {
    // I = J * Q + R
    let comp1 = Formula::AtomicFormula(AtomicFormula::Comparison(Comparison {
        term: i.into(),
        guards: vec![Guard {
            relation: Relation::Equal,
            term: GeneralTerm::IntegerTerm(IntegerTerm::BinaryOperation {
                op: BinaryOperator::Add,
                lhs: IntegerTerm::BinaryOperation {
                    op: BinaryOperator::Multiply,
                    lhs: IntegerTerm::Variable(j.name.clone()).into(),
                    rhs: IntegerTerm::Variable(q.name).into(),
                }
                .into(),
                rhs: IntegerTerm::Variable(r.name.clone()).into(),
            }),
        }],
    }));

    // J != 0 & R >= 0 & R < J
    let comp2 = Formula::conjoin(vec![
        Formula::AtomicFormula(AtomicFormula::Comparison(Comparison {
            term: j.clone().into(),
            guards: vec![Guard {
                relation: Relation::NotEqual,
                term: GeneralTerm::IntegerTerm(IntegerTerm::Numeral(0)),
            }],
        })),
        Formula::AtomicFormula(AtomicFormula::Comparison(Comparison {
            term: r.clone().into(),
            guards: vec![Guard {
                relation: Relation::GreaterEqual,
                term: GeneralTerm::IntegerTerm(IntegerTerm::Numeral(0)),
            }],
        })),
        Formula::AtomicFormula(AtomicFormula::Comparison(Comparison {
            term: r.into(),
            guards: vec![Guard {
                relation: Relation::Less,
                term: j.into(),
            }],
        })),
    ]);

    Formula::conjoin(vec![comp1, valti, valtj, comp2])
}

// Gringo 6 compliant integer division and modulo.
// Follows Verifying Tight Logic Programs with Anthem and Vampire
// Division: exists I J Q R (F4(IJQR) & Z = Q)
// Modulo:   exists I J Q R (F4(IJQR) & Z = R)
fn construct_gsix_partial_function_formula(
    valti: Formula,
    valtj: Formula,
    binop: asp::BinaryOperator,
    i: Variable,
    j: Variable,
    z: Variable,
) -> Formula {
    assert_eq!(i.sort, Sort::Integer);
    assert_eq!(j.sort, Sort::Integer);

    let mut taken_vars = IndexSet::new();
    taken_vars.insert(z.clone());
    let qvar = Variable {
        name: taken_vars.choose_fresh_variable("Q"),
        sort: Sort::Integer,
    };
    let rvar = Variable {
        name: taken_vars.choose_fresh_variable("R"),
        sort: Sort::Integer,
    };

    let quantification = Quantification {
        quantifier: Quantifier::Exists,
        variables: vec![i.clone(), j.clone(), qvar.clone(), rvar.clone()],
    };

    match binop {
        // exists I J Q R (F4(IJQR) & Z = Q)
        asp::BinaryOperator::Divide => Formula::QuantifiedFormula {
            quantification,
            formula: Formula::BinaryFormula {
                connective: BinaryConnective::Conjunction,
                lhs: division_helper_f4(valti, valtj, i, j, qvar.clone(), rvar).into(),
                rhs: Formula::AtomicFormula(AtomicFormula::Comparison(Comparison {
                    term: z.into(),
                    guards: vec![Guard {
                        relation: Relation::Equal,
                        term: qvar.into(),
                    }],
                }))
                .into(),
            }
            .into(),
        },

        // exists I J Q R (F4(IJQR) & Z = R)
        asp::BinaryOperator::Modulo => Formula::QuantifiedFormula {
            quantification,
            formula: Formula::BinaryFormula {
                connective: BinaryConnective::Conjunction,
                lhs: division_helper_f4(valti, valtj, i, j, qvar, rvar.clone()).into(),
                rhs: Formula::AtomicFormula(AtomicFormula::Comparison(Comparison {
                    term: z.into(),
                    guards: vec![Guard {
                        relation: Relation::Equal,
                        term: rvar.into(),
                    }],
                }))
                .into(),
            }
            .into(),
        },

        _ => unreachable!("division and modulo are the only supported partial functions"),
    }
}

// c(t1, ..., tk)
// exists X1 ... Xk ( val_t1(X1) & ... val_tk(Xk) & Z = c(X1, ..., Xk) )
fn construct_herbrand_formula(
    symbol: String,
    terms: Vec<asp::Term>,
    z: Variable,
    taken_variables: IndexSet<Variable>,
    dialect: Dialect,
) -> Formula {
    let fresh_var_names = taken_variables.choose_fresh_variables("X", terms.len());
    let variables: Vec<Variable> = fresh_var_names
        .iter()
        .map(|n| Variable {
            name: n.into(),
            sort: Sort::General,
        })
        .collect();

    // val_t1(X1) & ... val_tk(Xk)
    let mut formulas = Vec::new();
    for (i, term) in terms.iter().enumerate() {
        formulas.push(val(
            term.clone(),
            variables[i].clone(),
            taken_variables.clone(),
            dialect,
        ));
    }

    // Z = c(X1, ..., Xk)
    formulas.push(Formula::AtomicFormula(AtomicFormula::Comparison(
        Comparison {
            term: GeneralTerm::Variable(z.name),
            guards: vec![Guard {
                relation: Relation::Equal,
                term: GeneralTerm::Function(Function {
                    function_symbol: symbol,
                    sort: Sort::Symbol,
                    terms: fresh_var_names
                        .iter()
                        .map(|n| GeneralTerm::Variable(n.into()))
                        .collect(),
                }),
            }],
        },
    )));

    let inner = Formula::conjoin(formulas);

    Formula::QuantifiedFormula {
        quantification: Quantification {
            quantifier: Quantifier::Exists,
            variables,
        },
        formula: inner.into(),
    }
}

// val_t(Z)
fn val(
    t: asp::Term,
    z: Variable,
    taken_variables: IndexSet<Variable>,
    dialect: Dialect,
) -> Formula {
    let mut taken_variables = taken_variables;
    taken_variables.insert(z.clone());
    for var in t.variables().iter() {
        taken_variables.insert(Variable {
            name: var.to_string(),
            sort: Sort::General,
        });
    }

    let fresh_int_vars = choose_fresh_ijk(taken_variables.clone());

    for (_, value) in fresh_int_vars.iter() {
        taken_variables.insert(value.clone());
    }

    match t {
        asp::Term::BasicSymbol(_) | asp::Term::Variable(_) => construct_equality_formula(t, z),
        asp::Term::HerbrandFunction { symbol, terms } => {
            construct_herbrand_formula(symbol, terms, z, taken_variables, dialect)
        }
        asp::Term::UnaryOperation { op, arg } => match op {
            asp::UnaryOperator::Negative => {
                let lhs = asp::Term::BasicSymbol(asp::BasicSymbol::Numeral(0)); // Shorthand for 0 - t
                let valti = val(
                    lhs,
                    fresh_int_vars["I"].clone(),
                    taken_variables.clone(),
                    dialect,
                ); // val_t1(I)
                let valtj = val(*arg, fresh_int_vars["J"].clone(), taken_variables, dialect); // val_t2(J)
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
                let valti = val(
                    *arg,
                    fresh_int_vars["I"].clone(),
                    taken_variables.clone(),
                    dialect,
                ); // val_t1(I)
                construct_absolute_value_formula(valti, fresh_int_vars["I"].clone(), z)
            }
        },
        asp::Term::BinaryOperation { op, lhs, rhs } => {
            let valti = val(
                *lhs,
                fresh_int_vars["I"].clone(),
                taken_variables.clone(),
                dialect,
            ); // val_t1(I)
            let valtj = val(*rhs, fresh_int_vars["J"].clone(), taken_variables, dialect); // val_t2(J)
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
                asp::BinaryOperator::Divide | asp::BinaryOperator::Modulo => match dialect {
                    Dialect::GringoFive => construct_gfive_partial_function_formula(
                        valti,
                        valtj,
                        op,
                        fresh_int_vars["I"].clone(),
                        fresh_int_vars["J"].clone(),
                        fresh_int_vars["K"].clone(),
                        z,
                    ),
                    Dialect::GringoSix => construct_gsix_partial_function_formula(
                        valti,
                        valtj,
                        op,
                        fresh_int_vars["I"].clone(),
                        fresh_int_vars["J"].clone(),
                        z,
                    ),
                },
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
fn valtz(mut terms: Vec<asp::Term>, mut variables: Vec<Variable>, dialect: Dialect) -> Formula {
    Formula::conjoin(
        terms
            .drain(..)
            .zip(variables.drain(..))
            .map(|(t, v)| val(t, v, IndexSet::new(), dialect)),
    )
}

// Translate a body literal
fn tau_b_literal(l: asp::Literal, taken_vars: IndexSet<Variable>, dialect: Dialect) -> Formula {
    let atom = l.atom;
    let terms = atom.terms;
    let arity = terms.len();
    let varnames = taken_vars.choose_fresh_variables("Z", arity);

    // val_t1(Z1) & val_t2(Z2) & ... & val_tk(Zk)
    let vars: Vec<Variable> = varnames
        .iter()
        .map(|s| Variable {
            name: s.to_string(),
            sort: Sort::General,
        })
        .collect();
    let val_t_z = valtz(terms, vars.clone(), dialect);

    // Compute p(Z1, Z2, ..., Zk)
    let var_terms: Vec<GeneralTerm> = vars.iter().cloned().map(GeneralTerm::from).collect();
    let p_zk = Formula::AtomicFormula(AtomicFormula::Atom(Atom {
        predicate_symbol: atom.predicate_symbol,
        terms: var_terms,
    }));

    // Compute tau^b(B) minus the existential quantifier
    let inner = match l.sign {
        asp::Sign::NoSign => Formula::BinaryFormula {
            connective: BinaryConnective::Conjunction,
            lhs: val_t_z.into(),
            rhs: p_zk.into(),
        },

        asp::Sign::Negation => Formula::BinaryFormula {
            connective: BinaryConnective::Conjunction,
            lhs: val_t_z.into(),
            rhs: Formula::UnaryFormula {
                connective: UnaryConnective::Negation,
                formula: p_zk.into(),
            }
            .into(),
        },

        asp::Sign::DoubleNegation => Formula::BinaryFormula {
            connective: BinaryConnective::Conjunction,
            lhs: val_t_z.into(),
            rhs: Formula::UnaryFormula {
                connective: UnaryConnective::Negation,
                formula: Formula::UnaryFormula {
                    connective: UnaryConnective::Negation,
                    formula: p_zk.into(),
                }
                .into(),
            }
            .into(),
        },
    };

    if arity > 0 {
        Formula::QuantifiedFormula {
            quantification: Quantification {
                quantifier: Quantifier::Exists,
                variables: vars,
            },
            formula: inner.into(),
        }
    } else {
        let mut prep = [PREPROCESS].concat().into_iter().compose();
        inner.apply_fixpoint(&mut prep)
    }
}

// Translate a body comparison
fn tau_b_comparison(
    c: asp::Comparison,
    taken_vars: IndexSet<Variable>,
    dialect: Dialect,
) -> Formula {
    let varnames = taken_vars.choose_fresh_variables("Z", 2);

    // Compute val_t1(Z1) & val_t2(Z2)
    let term_z1 = GeneralTerm::Variable(varnames[0].clone());
    let term_z2 = GeneralTerm::Variable(varnames[1].clone());
    let var_z1 = Variable {
        sort: Sort::General,
        name: varnames[0].clone(),
    };
    let var_z2 = Variable {
        sort: Sort::General,
        name: varnames[1].clone(),
    };

    let valtz = Formula::BinaryFormula {
        connective: BinaryConnective::Conjunction,
        lhs: val(c.lhs, var_z1.clone(), taken_vars.clone(), dialect).into(),
        rhs: val(c.rhs, var_z2.clone(), taken_vars, dialect).into(),
    };

    Formula::QuantifiedFormula {
        quantification: Quantification {
            quantifier: Quantifier::Exists,
            variables: vec![var_z1, var_z2],
        },
        formula: Formula::BinaryFormula {
            connective: BinaryConnective::Conjunction,
            lhs: valtz.into(),
            rhs: Formula::AtomicFormula(AtomicFormula::Comparison(Comparison {
                term: term_z1,
                guards: vec![Guard {
                    relation: Relation::from(c.relation),
                    term: term_z2,
                }],
            }))
            .into(),
        }
        .into(),
    }
}

// Translate a body literal or comparison
fn tau_b(f: asp::AtomicFormula, dialect: Dialect) -> Formula {
    let mut taken_vars = IndexSet::new();
    for var in f.variables().iter() {
        taken_vars.insert(Variable {
            name: var.to_string(),
            sort: Sort::General,
        });
    }
    match f {
        asp::AtomicFormula::Literal(l) => tau_b_literal(l, taken_vars, dialect),
        asp::AtomicFormula::Comparison(c) => tau_b_comparison(c, taken_vars, dialect),
    }
}

// Translate a rule body
fn tau_body(b: asp::Body, dialect: Dialect) -> fol::Formula {
    let mut formulas = Vec::<fol::Formula>::new();
    for f in b.formulas.iter() {
        formulas.push(tau_b(f.clone(), dialect));
    }
    fol::Formula::conjoin(formulas)
}

// Translate a rule using a pre-defined list of global variables
pub(crate) fn tau_star_rule(r: asp::Rule, globals: &[String], dialect: Dialect) -> Formula {
    let mut prep = [PREPROCESS].concat().into_iter().compose();

    let body = tau_body(r.body.clone(), dialect);

    match r.head.predicate() {
        Some(predicate) => {
            // V1, ..., Vk
            let kvars = if predicate.arity > 0 {
                globals[0..predicate.arity]
                    .iter()
                    .map(|s| Variable {
                        name: s.to_string(),
                        sort: Sort::General,
                    })
                    .collect()
            } else {
                Vec::new()
            };

            // val_t1(V1) & ... & val_tk(Vk)
            let val_t_v = match r.head.terms() {
                Some(terms) => valtz(terms.to_vec(), kvars.clone(), dialect),
                None => Formula::AtomicFormula(AtomicFormula::Truth),
            };

            let consequent = if predicate.arity > 0 {
                // Atom with variables in the head
                Formula::AtomicFormula(AtomicFormula::Atom(Atom {
                    predicate_symbol: predicate.symbol,
                    terms: kvars
                        .iter()
                        .map(|v| GeneralTerm::Variable(v.name.clone()))
                        .collect(),
                }))
            } else {
                // Propositional atom in the head
                Formula::AtomicFormula(AtomicFormula::Atom(Atom {
                    predicate_symbol: predicate.symbol,
                    terms: vec![],
                }))
            };

            let antecedent = if r.is_choice_rule() {
                // Choice rule
                // not not p(V)
                let dbl_neg_head = Formula::UnaryFormula {
                    connective: UnaryConnective::Negation,
                    formula: Formula::UnaryFormula {
                        connective: UnaryConnective::Negation,
                        formula: consequent.clone().into(),
                    }
                    .into(),
                };

                Formula::BinaryFormula {
                    connective: BinaryConnective::Conjunction,
                    lhs: Formula::BinaryFormula {
                        connective: BinaryConnective::Conjunction,
                        lhs: val_t_v.into(),
                        rhs: body.into(),
                    }
                    .into(),
                    rhs: dbl_neg_head.into(),
                }
            } else {
                // Basic rule
                Formula::BinaryFormula {
                    connective: BinaryConnective::Conjunction,
                    lhs: val_t_v.into(),
                    rhs: body.into(),
                }
            };

            Formula::BinaryFormula {
                connective: BinaryConnective::Implication,
                lhs: antecedent.into(),
                rhs: consequent.into(),
            }
        }
        // Handles the case when we have a rule with an empty head
        None => Formula::BinaryFormula {
            connective: BinaryConnective::Implication,
            lhs: body.into(),
            rhs: Formula::AtomicFormula(AtomicFormula::Falsity).into(),
        },
    }
    .universal_closure()
    .apply_fixpoint(&mut prep)
}

// For each rule, produce a formula: forall G V ( val_t(V) & tau_body(Body) -> p(V) )
// Where G is all variables from the original rule
// and V is the set of fresh variables replacing t within p
fn tau_star(p: Program, dialect: Dialect) -> Theory {
    let globals = choose_fresh_global_variables(&p);
    let mut formulas: Vec<Formula> = vec![]; // { forall G V ( val_t(V) & tau^B(Body) -> p(V) ), ... }
    for r in p.rules {
        formulas.push(tau_star_rule(r, &globals, dialect));
    }
    Theory { formulas }
}

pub trait TauStar {
    type Output;

    fn tau_star(self, dialect: Dialect) -> Self::Output;
}

impl TauStar for Program {
    type Output = Theory;

    fn tau_star(self, dialect: Dialect) -> Self::Output {
        tau_star(self, dialect)
    }
}

#[cfg(test)]
mod tests {
    use indexmap::IndexSet;

    use crate::{
        command_line::arguments::Dialect, translating::formula_representation::tau_star::valtz,
    };

    use super::{choose_fresh_global_variables, tau_b, tau_star, val};

    #[test]
    fn test_choose_variables() {
        for (program, variables) in [
            ("p(X) :- q(X,Y).", Vec::from_iter(["V1"])),
            ("p(X,V1) :- q(X,V3).", Vec::from_iter(["V4", "V5"])),
            (
                "p(V2) :- q(X,Y). q(X,Y,Z) :- X = Y, Y = Z.",
                Vec::from_iter(["V3", "V4", "V5"]),
            ),
        ] {
            let chosen = choose_fresh_global_variables(&program.parse().unwrap());
            let target: Vec<String> = variables.iter().map(|v| v.to_string()).collect();
            assert_eq!(chosen, target);
        }
    }

    #[test]
    fn test_val() {
        for (term, dialect, var, target) in [
            (
                "f(a)",
                Dialect::GringoFive,
                "Z1",
                "exists X$g (X$g = a and Z1$g = f$s(X$g))",
            ),
            (
                "X + 1",
                Dialect::GringoFive,
                "Z1",
                "exists I$i J$i (Z1$g = I$i + J$i and I$i = X and J$i = 1)",
            ),
            (
                "3 - 5",
                Dialect::GringoFive,
                "Z1",
                "exists I$i J$i (Z1$g = I$i - J$i and I$i = 3 and J$i = 5)",
            ),
            (
                "Xanadu/Yak",
                Dialect::GringoFive,
                "Z1",
                "exists I$i J$i K$i (I$i = Xanadu and J$i = Yak and K$i * |J$i| <= |I$i| < (K$i + 1) * |J$i| and ((I$i * J$i >= 0 and Z1 = K$i) or (I$i * J$i < 0 and Z1 = -K$i)))",
            ),
            (
                "X \\ 3",
                Dialect::GringoFive,
                "Z1",
                "exists I$i J$i K$i (I$i = X and J$i = 3 and K$i * |J$i| <= |I$i| < (K$i + 1) * |J$i| and ((I$i * J$i >= 0 and Z1 = I$i - K$i * J$i) or (I$i * J$i < 0 and Z1 = I$i + K$i * J$i)))",
            ),
            (
                "X..Y",
                Dialect::GringoFive,
                "Z",
                "exists I$i J$i K$i (I$i = X and J$i = Y and Z$g = K$i and I$i <= K$i <= J$i)",
            ),
            (
                "X+1..Y",
                Dialect::GringoFive,
                "Z1",
                "exists I$i J$i K$i ((exists I1$i J1$i (I$i = I1$i + J1$i and I1$i = X and J1$i = 1)) and J$i = Y and Z1 = K$i and I$i <= K$i <= J$i)",
            ),
        ] {
            let left = val(
                term.parse().unwrap(),
                var.parse().unwrap(),
                IndexSet::new(),
                dialect,
            );
            let right = target.parse().unwrap();

            assert!(
                left == right,
                "assertion `left == right` failed:\n left:\n{left}\n right:\n{right}"
            );
        }
    }

    #[test]
    fn test_valtz() {
        for (term, dialect, var, target) in [
            (
                "X + 1",
                Dialect::GringoFive,
                "Z1",
                "exists I$i J$i (Z1$g = I$i + J$i and I$i = X and J$i = 1)",
            ),
            (
                "3 - (1..5)",
                Dialect::GringoFive,
                "Z1",
                "exists I$i J$i (Z1$g = I$i - J$i and I$i = 3 and exists I1$i J1$i K1$i (I1$i = 1 and J1$i = 5 and J$i = K1$i and I1$i <= K1$i <= J1$i))",
            ),
        ] {
            let left = valtz(
                vec![term.parse().unwrap()],
                vec![var.parse().unwrap()],
                dialect,
            );
            let right = target.parse().unwrap();

            assert!(
                left == right,
                "assertion `left == right` failed:\n left:\n{left}\n right:\n{right}"
            );
        }
    }

    #[test]
    fn test_tau_b() {
        for (src, dialect, target) in [
            ("p(t)", Dialect::GringoFive, "exists Z (Z = t and p(Z))"),
            (
                "not p(t)",
                Dialect::GringoFive,
                "exists Z (Z = t and not p(Z))",
            ),
            (
                "X < 1..5",
                Dialect::GringoFive,
                "exists Z Z1 (Z = X and exists I$i J$i K$i (I$i = 1 and J$i = 5 and Z1 = K$i and I$i <= K$i <= J$i) and Z < Z1)",
            ),
            (
                "not not p(t)",
                Dialect::GringoFive,
                "exists Z (Z = t and not not p(Z))",
            ),
            ("not not x", Dialect::GringoFive, "not not x"),
            (
                "not p(X,5)",
                Dialect::GringoFive,
                "exists Z Z1 (Z = X and Z1 = 5 and not p(Z,Z1))",
            ),
            (
                "not p(X,0-5)",
                Dialect::GringoFive,
                "exists Z Z1 (Z = X and exists I$i J$i (Z1 = I$i - J$i and I$i = 0 and J$i = 5) and not p(Z,Z1))",
            ),
            (
                "p(X,-1..5)",
                Dialect::GringoFive,
                "exists Z Z1 (Z = X and exists I$i J$i K$i (I$i = -1 and J$i = 5 and Z1 = K$i and I$i <= K$i <= J$i) and p(Z,Z1))",
            ),
            (
                "p(X,-(1..5))",
                Dialect::GringoFive,
                "exists Z Z1 (Z = X and exists I$i J$i (Z1 = I$i - J$i and I$i = 0 and exists I1$i J1$i K1$i (I1$i = 1 and J1$i = 5  and J$i = K1$i and I1$i <= K1$i <= J1$i)) and p(Z,Z1))",
            ),
            (
                "p(1/0)",
                Dialect::GringoFive,
                "exists Z (exists I$i J$i K$i (I$i = 1 and J$i = 0 and (K$i * |J$i| <= |I$i| < (K$i+1) * |J$i|) and ((I$i * J$i >= 0 and Z = K$i) or (I$i*J$i < 0 and Z = -K$i)) ) and p(Z))",
            ),
            (
                "X / Y > 5",
                Dialect::GringoSix,
                "exists Z Z1 (exists I$i J$i Q$i R$i (I$i = J$i * Q$i + R$i and I$i = X and J$i = Y and (J$i != 0 and R$i >= 0 and R$i < J$i) and Z = Q$i) and Z1 = 5 and Z > Z1)",
            ),
            (
                "X \\ Y > 5",
                Dialect::GringoSix,
                "exists Z Z1 (exists I$i J$i Q$i R$i (I$i = J$i * Q$i + R$i and I$i = X and J$i = Y and (J$i != 0 and R$i >= 0 and R$i < J$i) and Z = R$i) and Z1 = 5 and Z > Z1)",
            ),
        ] {
            let left = tau_b(src.parse().unwrap(), dialect);
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
            (
                "p(a). p(b). q(X, Y) :- p(X), p(Y).",
                "forall V1 (V1 = a -> p(V1)). forall V1 (V1 = b -> p(V1)). forall V1 V2 X Y (V1 = X and V2 = Y and (exists Z (Z = X and p(Z)) and exists Z (Z = Y and p(Z))) -> q(V1,V2)).",
            ),
            ("p.", "#true -> p."),
            ("q :- not p.", "not p -> q."),
            (
                "{q(X)} :- p(X).",
                "forall V1 X (V1 = X and exists Z (Z = X and p(Z)) and not not q(V1) -> q(V1)).",
            ),
            (
                "{q(V)} :- p(V).",
                "forall V V1 (V1 = V and exists Z (Z = V and p(Z)) and not not q(V1) -> q(V1)).",
            ),
            (
                "{q(V+1)} :- p(V), not q(X).",
                "forall V V1 X (exists I$i J$i (V1 = I$i + J$i and I$i = V and J$i = 1) and (exists Z (Z = V and p(Z)) and exists Z (Z = X and not q(Z))) and not not q(V1) -> q(V1)).",
            ),
            (
                ":- p(X,3), not q(X,a).",
                "forall X (exists Z Z1 (Z = X and Z1 = 3 and p(Z,Z1)) and exists Z Z1 (Z = X and Z1 = a and not q(Z,Z1)) -> #false).",
            ),
            (":- p.", "p -> #false."),
            ("{p} :- q.", "q and not not p -> p."),
            ("{p}.", "not not p -> p."),
            ("{p(5)}.", "forall V1 (V1 = 5 and not not p(V1) -> p(V1))."),
            ("p. q.", "#true -> p. #true -> q."),
            (
                "{ra(X,a)} :- ta(X). ra(5,a).",
                "forall V1 V2 X (V1 = X and V2 = a and exists Z (Z = X and ta(Z)) and not not ra(V1, V2) -> ra(V1, V2)). forall V1 V2 (V1 = 5 and V2 = a -> ra(V1, V2)).",
            ),
        ] {
            let left = tau_star(src.parse().unwrap(), Dialect::GringoFive);
            let right = target.parse().unwrap();

            assert!(
                left == right,
                "assertion `left == right` failed:\n left:\n{left}\n right:\n{right}"
            );
        }
    }
}
