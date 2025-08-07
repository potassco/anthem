use {
    crate::syntax_tree::{
        asp::{
            Atom, AtomicFormula, BinaryOperator, Body, Head, Literal, PrecomputedTerm, Predicate,
            Program, Rule, Sign, Term, Variable,
        },
        fol::{self, UserGuide},
    },
    indexmap::IndexSet,
};

const DOMAIN_PREDICATE_NAME: &str = "dom";
const DIFF_PREDICATE_NAME: &str = "diff";
const UNSAT_PREDICATE_NAME: &str = "unsat";

pub fn generate_external_counterexample_program(
    user_guide: &UserGuide,
    mut left: Program,
    right: Program,
) -> Program {
    let mut functions = left.function_constants();
    functions.extend(right.function_constants());

    let mut input_program = generate_input_program(user_guide, functions);
    let mut diff_program = generate_diff_program(user_guide, false, right.has_constraint());
    let mut right_transformed = convert_program(user_guide, right);

    let mut rules = vec![];
    rules.append(&mut input_program.rules);
    rules.append(&mut left.rules);
    rules.append(&mut right_transformed.rules);
    rules.append(&mut diff_program.rules);

    Program { rules }
}

pub fn generate_guess_and_check_programs(
    user_guide: &UserGuide,
    mut left: Program,
    right: Program,
) -> (Program, Program) {
    let mut functions = left.function_constants();
    functions.extend(right.function_constants());

    // guess program
    let mut input_program = generate_input_program(user_guide, functions);
    let mut map_program = generate_holds_map(user_guide);

    let mut guess_rules = vec![];
    guess_rules.append(&mut input_program.rules);
    guess_rules.append(&mut left.rules);
    guess_rules.append(&mut map_program.rules);

    // check program
    let mut diff_program = generate_diff_program(user_guide, true, right.has_constraint());
    let mut right_transformed = convert_program(user_guide, right);
    let mut projection_program = generate_holds_projection(user_guide);

    let mut check_rules = vec![];
    check_rules.append(&mut right_transformed.rules);
    check_rules.append(&mut diff_program.rules);
    check_rules.append(&mut projection_program.rules);

    (
        Program { rules: guess_rules },
        Program { rules: check_rules },
    )
}

fn generate_input_program(user_guide: &UserGuide, functions: IndexSet<String>) -> Program {
    let mut rules = vec![];

    rules.append(&mut generate_domain_facts(functions).rules);
    rules.append(&mut generate_input_generator(user_guide).rules);

    Program { rules }
}

// dom(1..n).
// TODO: also include all ground terms as input elements (needs programs as inputs)
fn generate_domain_facts(functions: IndexSet<String>) -> Program {
    let interval = Term::BinaryOperation {
        op: BinaryOperator::Interval,
        lhs: Box::new(Term::PrecomputedTerm(PrecomputedTerm::Numeral(1))),
        rhs: Box::new(Term::PrecomputedTerm(PrecomputedTerm::Symbol(
            "n".to_string(),
        ))),
    };

    let head = Head::Basic(Atom {
        predicate_symbol: DOMAIN_PREDICATE_NAME.to_string(),
        terms: vec![interval],
    });

    let mut rules: Vec<Rule> = functions
        .into_iter()
        .map(|function| Rule {
            head: Head::Basic(Atom {
                predicate_symbol: DOMAIN_PREDICATE_NAME.to_string(),
                terms: vec![Term::PrecomputedTerm(PrecomputedTerm::Symbol(function))],
            }),
            body: Body { formulas: vec![] },
        })
        .collect();

    rules.push(Rule {
        head,
        body: Body { formulas: vec![] },
    });

    Program { rules }
}

// for all input predicates p in user_guide:
// { p(X) } :- dom(X).
fn generate_input_generator(user_guide: &UserGuide) -> Program {
    fn domain_choice(predicate: Predicate) -> Rule {
        let variables: Vec<Term> = (1..predicate.arity + 1)
            .map(|i| Term::Variable(Variable(format!("X{}", i))))
            .collect();

        let head = Head::Choice(Atom {
            predicate_symbol: predicate.symbol,
            terms: variables.clone(),
        });

        fn domain_literal(var: Term) -> Literal {
            Literal {
                sign: Sign::NoSign,
                atom: Atom {
                    predicate_symbol: DOMAIN_PREDICATE_NAME.to_string(),
                    terms: vec![var],
                },
            }
        }

        let formulas: Vec<AtomicFormula> = variables
            .into_iter()
            .map(|var| AtomicFormula::Literal(domain_literal(var)))
            .collect();

        Rule {
            head,
            body: Body { formulas },
        }
    }

    let rules = user_guide
        .input_predicates()
        .into_iter()
        .map(|predicate| domain_choice(Predicate::from(predicate)))
        .collect();

    Program { rules }
}

fn generate_diff_program(
    user_guide: &UserGuide,
    use_guess_and_check: bool,
    has_constraint: bool,
) -> Program {
    let mut rules = vec![];

    rules.append(&mut generate_diff_rules(user_guide, has_constraint).rules);
    rules.append(&mut generate_diff_constraint(use_guess_and_check).rules);

    Program { rules }
}

// :- not diff. or
// :- diff. for guess and check
fn generate_diff_constraint(use_guess_and_check: bool) -> Program {
    let sign = if use_guess_and_check {
        Sign::NoSign
    } else {
        Sign::Negation
    };

    let constraint = Rule {
        head: Head::Falsity,
        body: Body {
            formulas: vec![AtomicFormula::Literal(Literal {
                sign,
                atom: Atom {
                    predicate_symbol: DIFF_PREDICATE_NAME.to_string(),
                    terms: vec![],
                },
            })],
        },
    };

    Program {
        rules: vec![constraint],
    }
}

// for every output predicate p in user_guide:
// diff :- p, not p'.
// diff :- not p, p'.
// and rule for unsat predicate: diff :- unsat.
fn generate_diff_rules(user_guide: &UserGuide, has_constraint: bool) -> Program {
    fn diff_rule(predicate: Predicate) -> Vec<Rule> {
        let mut rules = vec![];

        let atom = Atom {
            predicate_symbol: predicate.symbol,
            terms: (1..predicate.arity + 1)
                .map(|i| Term::Variable(Variable(format!("X{}", i))))
                .collect(),
        };

        let head = Head::Basic(Atom {
            predicate_symbol: DIFF_PREDICATE_NAME.to_string(),
            terms: vec![],
        });

        fn diff_body(left: Atom, right: Atom) -> Body {
            Body {
                formulas: vec![
                    AtomicFormula::Literal(Literal {
                        sign: Sign::NoSign,
                        atom: left,
                    }),
                    AtomicFormula::Literal(Literal {
                        sign: Sign::Negation,
                        atom: right,
                    }),
                ],
            }
        }

        rules.push(Rule {
            head: head.clone(),
            body: diff_body(atom.clone(), convert_atom(atom.clone())),
        });
        rules.push(Rule {
            head,
            body: diff_body(convert_atom(atom.clone()), atom),
        });

        rules
    }

    let mut rules: Vec<Rule> = user_guide
        .output_predicates()
        .into_iter()
        .flat_map(|predicate| diff_rule(Predicate::from(predicate)))
        .collect();

    if has_constraint {
        rules.push(Rule {
            head: Head::Basic(Atom {
                predicate_symbol: DIFF_PREDICATE_NAME.to_string(),
                terms: vec![],
            }),
            body: Body {
                formulas: vec![AtomicFormula::Literal(Literal {
                    sign: Sign::NoSign,
                    atom: Atom {
                        predicate_symbol: UNSAT_PREDICATE_NAME.to_string(),
                        terms: vec![],
                    },
                })],
            },
        });
    }

    Program { rules }
}

fn convert_program(user_guide: &UserGuide, program: Program) -> Program {
    let rules = program
        .rules
        .into_iter()
        .map(|r| convert_rule(user_guide, r))
        .collect();

    Program { rules }
}

// { p } :- Body. -> p'    :- Body', p.
//       :- Body. -> unsat :- Body'.
//   p   :- Body. -> p'    :- Body'.
fn convert_rule(user_guide: &UserGuide, rule: Rule) -> Rule {
    match rule {
        Rule {
            head: Head::Choice(atom),
            body,
        } => convert_choice_rule(
            user_guide,
            Rule {
                head: Head::Choice(atom),
                body,
            },
        ),
        Rule { head, body } => {
            let head = match head {
                Head::Falsity => get_unsat_head(),
                Head::Basic(atom) => {
                    if user_guide
                        .public_predicates()
                        .contains(&fol::Predicate::from(atom.predicate()))
                    {
                        Head::Basic(convert_atom(atom))
                    } else {
                        Head::Basic(atom)
                    }
                }
                Head::Choice(_) => unreachable!(),
            };

            Rule {
                head,
                body: convert_rule_body(user_guide, body),
            }
        }
    }
}

// convert { p } :- Body. to
// p' :- Body', p. if p is output predicate where Body' is the converted body
fn convert_choice_rule(user_guide: &UserGuide, rule: Rule) -> Rule {
    let atom = rule.head.atom().unwrap();

    let head = Head::Basic(convert_atom(atom.clone()));

    let mut body = convert_rule_body(user_guide, rule.body);
    body.formulas.push(AtomicFormula::Literal(Literal {
        sign: Sign::NoSign,
        atom,
    }));

    Rule { head, body }
}

// get new head for constraints
fn get_unsat_head() -> Head {
    Head::Basic(Atom {
        predicate_symbol: UNSAT_PREDICATE_NAME.to_string(),
        terms: vec![],
    })
}

// convert each literal in a body
fn convert_rule_body(user_guide: &UserGuide, body: Body) -> Body {
    let formulas = body
        .into_iter()
        .map(|f| match f {
            AtomicFormula::Literal(literal) => {
                AtomicFormula::Literal(convert_literal(user_guide, literal))
            }
            x => x,
        })
        .collect();

    Body { formulas }
}

// convert positive literals p(X) to
//   p'(X) if p is an output predicate
//   p(X)  else
// negative literals are unchanged
fn convert_literal(user_guide: &UserGuide, literal: Literal) -> Literal {
    match literal {
        Literal {
            sign: Sign::NoSign,
            atom,
        } => {
            let atom = if user_guide
                .output_predicates()
                .contains(&fol::Predicate::from(atom.predicate()))
            {
                convert_atom(atom)
            } else {
                atom
            };

            Literal {
                sign: Sign::NoSign,
                atom,
            }
        }
        l => l,
    }
}

// convert p(X) to p'(X)
fn convert_atom(atom: Atom) -> Atom {
    let mut predicate_symbol = atom.predicate_symbol;
    predicate_symbol.push('\'');
    Atom {
        predicate_symbol,
        terms: atom.terms,
    }
}

// turn p(X) into holds(p(X))
fn convert_atom_to_holds(atom: Atom) -> Atom {
    let atom_as_term = PrecomputedTerm::Symbol(format!("{}", atom));
    Atom {
        predicate_symbol: "holds".to_string(),
        terms: vec![Term::PrecomputedTerm(atom_as_term)],
    }
}

// holds(p(X)) :- p(X).
fn map_into_holds(predicate: Predicate) -> Rule {
    let variables: Vec<Term> = (1..predicate.arity + 1)
        .map(|i| Term::Variable(Variable(format!("X{}", i))))
        .collect();

    let atom = Atom {
        predicate_symbol: predicate.symbol,
        terms: variables,
    };

    let holds_atom = convert_atom_to_holds(atom.clone());

    Rule {
        head: Head::Basic(holds_atom),
        body: Body {
            formulas: vec![AtomicFormula::Literal(Literal {
                sign: Sign::NoSign,
                atom,
            })],
        },
    }
}

// holds mapping rules for each public predicate
fn generate_holds_map(user_guide: &UserGuide) -> Program {
    let rules: Vec<Rule> = user_guide
        .public_predicates()
        .into_iter()
        .map(|predicate| map_into_holds(Predicate::from(predicate)))
        .collect();

    Program { rules }
}

// p(X) :- holds(p(X)).
fn project_from_holds(predicate: Predicate) -> Rule {
    let variables: Vec<Term> = (1..predicate.arity + 1)
        .map(|i| Term::Variable(Variable(format!("X{}", i))))
        .collect();

    let atom = Atom {
        predicate_symbol: predicate.symbol,
        terms: variables,
    };

    let holds_atom = convert_atom_to_holds(atom.clone());

    Rule {
        head: Head::Basic(atom),
        body: Body {
            formulas: vec![AtomicFormula::Literal(Literal {
                sign: Sign::NoSign,
                atom: holds_atom,
            })],
        },
    }
}

// holds projection rule for each public predicate
fn generate_holds_projection(user_guide: &UserGuide) -> Program {
    let rules: Vec<Rule> = user_guide
        .public_predicates()
        .into_iter()
        .map(|predicate| project_from_holds(Predicate::from(predicate)))
        .collect();

    Program { rules }
}
