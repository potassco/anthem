use crate::syntax_tree::{
    asp::{
        Atom, AtomicFormula, BinaryOperator, Body, Head, Literal, PrecomputedTerm, Predicate,
        Program, Rule, Sign, Term, Variable,
    },
    fol::{self, UserGuide},
};

const DOMAIN_PREDICATE_NAME: &str = "dom";
const DIFF_PREDICATE_NAME: &str = "diff";

pub fn generate_external_counterexample_program(
    user_guide: &UserGuide,
    mut left: Program,
    right: Program,
) -> Program {
    let mut input_program = generate_input_program(user_guide);
    let mut diff_program = generate_diff_program(user_guide);
    let mut right_transformed = convert_program(user_guide, right);

    let mut rules = vec![];
    rules.append(&mut input_program.rules);
    rules.append(&mut left.rules);
    rules.append(&mut right_transformed.rules);
    rules.append(&mut diff_program.rules);

    Program { rules }
}

fn generate_input_program(user_guide: &UserGuide) -> Program {
    let mut rules = vec![];

    rules.append(&mut generate_domain_facts().rules);
    rules.append(&mut generate_input_generator(user_guide).rules);

    Program { rules }
}

// dom(1..n).
// TODO: also include all ground terms as input elements (needs programs as inputs)
fn generate_domain_facts() -> Program {
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

    Program {
        rules: vec![Rule {
            head,
            body: Body { formulas: vec![] },
        }],
    }
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

fn generate_diff_program(user_guide: &UserGuide) -> Program {
    let mut rules = vec![];

    rules.append(&mut generate_diff_rules(user_guide).rules);
    rules.append(&mut generate_diff_constraint().rules);

    Program { rules }
}

// :- not diff.
// TODO: add input for guess and check flag
fn generate_diff_constraint() -> Program {
    let constraint = Rule {
        head: Head::Falsity,
        body: Body {
            formulas: vec![AtomicFormula::Literal(Literal {
                sign: Sign::Negation,
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
// TODO: add input for guess and check flag
fn generate_diff_rules(user_guide: &UserGuide) -> Program {
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

    let rules: Vec<Rule> = user_guide
        .output_predicates()
        .into_iter()
        .flat_map(|predicate| diff_rule(Predicate::from(predicate)))
        .collect();

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

// convert { p } :- Body. in right program to
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

// get new head for constraints (i.e. unsat)
fn get_unsat_head() -> Head {
    Head::Basic(Atom {
        predicate_symbol: "unsat".to_string(),
        terms: vec![],
    })
}

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

fn convert_atom(atom: Atom) -> Atom {
    let mut predicate_symbol = atom.predicate_symbol;
    predicate_symbol.push('\'');
    Atom {
        predicate_symbol,
        terms: atom.terms,
    }
}
