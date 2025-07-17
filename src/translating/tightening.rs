use crate::syntax_tree::asp::{
    Atom, AtomicFormula, BinaryOperator, Body, Comparison, Head, Literal, PrecomputedTerm,
    Predicate, Program, Relation, Rule, Sign, Term, Variable,
};

pub fn tightening(program: Program) -> Program {
    // collect all predicates for creating projection rules
    let predicates = program.predicates();

    // tighten each rule
    let mut rules: Vec<Rule> = program.rules.into_iter().map(tighten_rule).collect();

    // create projection rules and add to tightened rules
    let projection_rules: Vec<Rule> = predicates.into_iter().map(projection_rule).collect();
    rules.extend(projection_rules);

    Program { rules }
}

fn tighten_rule(rule: Rule) -> Rule {
    // get a new variable new_var
    let new_var: Variable = rule.choose_fresh_variables("N", 1).first().unwrap().clone();

    match rule.head.clone() {
        Head::Basic(a) | Head::Choice(a) => {
            let mut terms = a.terms;

            // build the term new_var + 1
            let new_var_successor = Term::BinaryOperation {
                op: BinaryOperator::Add,
                lhs: Term::Variable(new_var.clone()).into(),
                rhs: Term::PrecomputedTerm(PrecomputedTerm::Numeral(1)).into(),
            };
            // add this term to the terms of the head predicate
            terms.push(new_var_successor);

            // head predicate is the same, only new_var + 1 is added as a new term
            let head = match rule.head {
                Head::Basic(_) => Head::Basic(Atom {
                    predicate_symbol: a.predicate_symbol,
                    terms,
                }),
                Head::Choice(_) => Head::Choice(Atom {
                    predicate_symbol: a.predicate_symbol,
                    terms,
                }),
                Head::Falsity => unreachable!(),
            };

            // tighten the rule body
            let body = tighten_body(rule.body, new_var);

            Rule { head, body }
        }
        // constraints are not changed by tightening
        Head::Falsity => rule,
    }
}

fn tighten_body(body: Body, new_var: Variable) -> Body {
    let mut formulas = Vec::new();

    for formula in body.formulas {
        match formula {
            // positive body literals are replaced
            AtomicFormula::Literal(Literal {
                sign: Sign::NoSign,
                atom,
            }) => {
                let mut terms = atom.terms;
                // new_var is added as an additional term to the atom
                terms.push(Term::Variable(new_var.clone()));
                let atom = Atom {
                    predicate_symbol: atom.predicate_symbol,
                    terms,
                };
                formulas.push(AtomicFormula::Literal(Literal {
                    sign: Sign::NoSign,
                    atom,
                }));
            }
            // non-positive literals and other body elements are unchanged
            x => formulas.push(x),
        }
    }

    // add the comparison formula as the last body element
    formulas.push(comparison_formula(new_var));

    Body { formulas }
}

// generates the comparison that var >= 0
fn comparison_formula(var: Variable) -> AtomicFormula {
    AtomicFormula::Comparison(Comparison {
        relation: Relation::GreaterEqual,
        lhs: Term::Variable(var),
        rhs: Term::PrecomputedTerm(PrecomputedTerm::Numeral(0)),
    })
}

fn projection_rule(predicate: Predicate) -> Rule {
    // variables X, X1, ..., Xn matching arity of the predicate
    let variables = predicate.choose_fresh_variables("X");
    let mut terms: Vec<Term> = variables.into_iter().map(Term::Variable).collect();

    // head is the predicate with the variables from above as terms
    let head = Head::Basic(Atom {
        predicate_symbol: predicate.symbol.clone(),
        terms: terms.clone(),
    });

    // for the body we need an additional variable N
    let new_var = Variable("N".to_string());

    // the body has the formulas
    let mut formulas: Vec<AtomicFormula> = Vec::new();
    // first, the predicate as a positive literal with the new variable N as an additional term
    terms.push(Term::Variable(new_var.clone()));
    formulas.push(AtomicFormula::Literal(Literal {
        sign: Sign::NoSign,
        atom: Atom {
            predicate_symbol: predicate.symbol,
            terms,
        },
    }));
    // second, the comparison formula for the new variable N
    formulas.push(comparison_formula(new_var));

    let body = Body { formulas };

    Rule { head, body }
}

#[cfg(test)]
mod tests {
    use super::tightening;
    use crate::syntax_tree::asp;

    #[test]
    fn test_tightening() {
        for (src, target) in [
            (
                "p :- q. q :- p.",
                "p(N+1) :- q(N), N >= 0. q(N+1) :- p(N), N >= 0. p :- p(N), N >= 0. q :- q(N), N >= 0.",
            ),
            (
                "p(X) :- q(X). q(X) :- p(X).",
                "p(X, N + 1) :- q(X, N), N >= 0. q(X, N + 1) :- p(X, N), N >= 0. p(X) :- p(X, N), N >= 0. q(X) :- q(X, N), N >= 0.",
            ),
            (
                "p(X) :- q(X), not r(X). q(X) :- p(X), r(X).",
                "p(X, N + 1) :- q(X, N), not r(X), N >= 0. q(X, N + 1) :- p(X, N), r(X, N), N >= 0. p(X) :- p(X, N), N >= 0. q(X) :- q(X, N), N >= 0. r(X) :- r(X, N), N >= 0.",
            ),
            (
                "p(N) :- q(N). q(N) :- p(N).",
                "p(N, N1 + 1) :- q(N, N1), N1 >= 0. q(N, N1 + 1) :- p(N, N1), N1 >= 0. p(X) :- p(X, N), N >= 0. q(X) :- q(X, N), N >= 0.",
            ),
            (
                "p(X,Y) :- q(X,Y). q(X,Y) :- p(X,Y).",
                "p(X, Y, N + 1) :- q(X, Y, N), N >= 0. q(X, Y, N + 1) :- p(X, Y, N), N >= 0. p(X, X1) :- p(X, X1, N), N >= 0. q(X, X1) :- q(X, X1, N), N >= 0.",
            ),
        ] {
            let program: asp::Program = src.parse().unwrap();
            let left = tightening(program);
            let right = target.parse().unwrap();

            assert!(
                left == right,
                "assertion `left == right` failed:\n left:\n{left}\n right:\n{right}"
            );
        }
    }
}
