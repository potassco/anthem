use crate::{
    convenience::choose_fresh_variable_names,
    syntax_tree::asp::{
        Atom, AtomicFormula, BinaryOperator, Body, Comparison, Head, Literal, PrecomputedTerm,
        Predicate, Program, Relation, Rule, Sign, Term, Variable,
    },
};

pub fn tightening(program: Program) -> Program {
    let predicates = program.predicates();

    let mut rules: Vec<Rule> = program.rules.into_iter().map(tighten_rule).collect();

    let projection_rules: Vec<Rule> = predicates.into_iter().map(projection_rule).collect();

    rules.extend(projection_rules);

    Program { rules }
}

fn tighten_rule(rule: Rule) -> Rule {
    let rule_vars = rule.variables();
    let taken_var_names: Vec<String> = rule_vars.into_iter().map(|v| v.to_string()).collect();
    let fresh_vars = choose_fresh_variable_names(taken_var_names, "N", 1);
    let new_var = Variable(fresh_vars.first().unwrap().to_string());

    match rule.head.clone() {
        Head::Basic(a) | Head::Choice(a) => {
            let mut terms = a.terms;

            let new_var_successor = Term::BinaryOperation {
                op: BinaryOperator::Add,
                lhs: Term::Variable(new_var.clone()).into(),
                rhs: Term::PrecomputedTerm(PrecomputedTerm::Numeral(1)).into(),
            };
            terms.push(new_var_successor);

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

            let body = tighten_body(rule.body, new_var);

            Rule { head, body }
        }
        Head::Falsity => rule,
    }
}

fn tighten_body(body: Body, new_var: Variable) -> Body {
    let mut formulas = Vec::new();

    for formula in body.formulas {
        match formula {
            AtomicFormula::Literal(Literal {
                sign: Sign::NoSign,
                atom,
            }) => {
                let mut terms = atom.terms;
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
            x => formulas.push(x),
        }
    }

    formulas.push(comparison_formula(new_var));

    Body { formulas }
}

fn comparison_formula(var: Variable) -> AtomicFormula {
    AtomicFormula::Comparison(Comparison {
        relation: Relation::GreaterEqual,
        lhs: Term::Variable(var),
        rhs: Term::PrecomputedTerm(PrecomputedTerm::Numeral(0)),
    })
}

fn projection_rule(predicate: Predicate) -> Rule {
    let variables = choose_fresh_variable_names(Vec::<String>::new(), "X", predicate.arity);
    let mut terms: Vec<Term> = variables
        .into_iter()
        .map(|v| Term::Variable(Variable(v)))
        .collect();

    let head = Head::Basic(Atom {
        predicate_symbol: predicate.symbol.clone(),
        terms: terms.clone(),
    });

    let new_var = Variable("N".to_string());
    terms.push(Term::Variable(new_var.clone()));

    let mut formulas = vec![AtomicFormula::Literal(Literal {
        sign: Sign::NoSign,
        atom: Atom {
            predicate_symbol: predicate.symbol,
            terms,
        },
    })];
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
