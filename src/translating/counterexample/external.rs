use crate::syntax_tree::{
    asp::{Atom, AtomicFormula, Body, Head, Literal, Program, Rule, Sign},
    fol::{self, UserGuide},
};

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
    let rules = vec![];

    Program { rules }
}

// dom(1..n).
// TODO: also include all ground terms as input elements (needs programs as inputs)
fn generate_domain_facts() -> Program {
    todo!()
}

// for all input predicates p in user_guide:
// { p(X) } :- dom(X).
fn generate_input_generator(user_guide: &UserGuide) -> Program {
    todo!()
}

fn generate_diff_program(user_guide: &UserGuide) -> Program {
    let rules = vec![];

    Program { rules }
}

// :- not diff.
// TODO: add input for guess and check flag
fn generate_difference_constraint() -> Program {
    todo!()
}

// for every output predicate p in user_guide:
// diff :- p, not p'.
// diff :- not p, p'.
// TODO: add input for guess and check flag
fn generate_diff_rules(user_guide: &UserGuide) -> Program {
    todo!()
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
                .input_predicates()
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
        Literal { sign, atom } => {
            let atom = if user_guide
                .public_predicates()
                .contains(&fol::Predicate::from(atom.predicate()))
            {
                convert_atom(atom)
            } else {
                atom
            };

            Literal { sign, atom }
        }
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
