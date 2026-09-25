use indexmap::IndexSet;

use crate::{
    convenience::variable_selection::VariableSelection,
    syntax_tree::asp::mini_gringo::{
        Atom, AtomicFormula, BasicSymbol, Body, Comparison, Head, Literal, Program, Relation, Rule,
        Sign, Term, Variable,
    },
};

// TODO: replace taken_vars parameter with mutable reference to taken_vars

// basic symbols in sigma_0 include symbolic constants, numerals, inf, and sup
// when we don't allow constructor functions, basic symbols are just the set of precomputed terms
fn leading_symbol_is_arithmetic_compatible(term: &BasicSymbol) -> bool {
    match term {
        BasicSymbol::Numeral(_) => true,
        BasicSymbol::Infimum | BasicSymbol::Symbol(_) | BasicSymbol::Supremum => false,
    }
}

fn term_replacement(
    term: Term,
    taken_vars: IndexSet<Variable>,
    within_arithmetic_scope: bool,
    rhs_of_numeric_equation: bool,
) -> (Term, Option<Comparison>) {
    match term {
        Term::HerbrandFunction { symbol, terms } => {
            if within_arithmetic_scope {
                let v = Variable(taken_vars.choose_fresh_variable("V"));
                let v_equals_t = Comparison {
                    relation: Relation::Equal,
                    lhs: Term::Variable(v.clone()),
                    rhs: Term::HerbrandFunction { symbol, terms },
                };
                (Term::Variable(v), Some(v_equals_t))
            } else {
                let mut v_equals_t = None;
                let mut new_terms = terms.clone();
                for (i, term) in terms.into_iter().enumerate() {
                    let (current, vt) = term_replacement(term, taken_vars.clone(), false, false);
                    if vt.is_some() {
                        new_terms[i] = current;
                        v_equals_t = vt;
                        break;
                    }
                }
                (
                    Term::HerbrandFunction {
                        symbol,
                        terms: new_terms,
                    },
                    v_equals_t,
                )
            }
        }
        Term::BasicSymbol(ref pct) => {
            // abnormal term, case a
            if within_arithmetic_scope && !leading_symbol_is_arithmetic_compatible(pct) {
                // no subterms in this case, so abnormality must be innermost
                let v = Variable(taken_vars.choose_fresh_variable("V"));
                let v_equals_t = Comparison {
                    relation: Relation::Equal,
                    lhs: Term::Variable(v.clone()),
                    rhs: term,
                };
                (Term::Variable(v), Some(v_equals_t))
            } else {
                (Term::BasicSymbol(pct.clone()), None)
            }

            // abnormal term, case b does not apply to pc terms
        }

        Term::Variable(var) => {
            // cases a and b of abnormal terms do not apply to variables
            (Term::Variable(var), None)
        }

        Term::UnaryOperation { op, arg } => {
            let (inner, vt) = term_replacement(*arg, taken_vars, true, false);
            (
                Term::UnaryOperation {
                    op,
                    arg: inner.into(),
                },
                vt,
            )
        }

        Term::BinaryOperation { op, lhs, rhs } => {
            let original_left = *lhs;
            let original_right = *rhs;
            let (left_term, left_vt) =
                term_replacement(original_left.clone(), taken_vars.clone(), true, false);
            if left_vt.is_some() {
                (
                    Term::BinaryOperation {
                        op,
                        lhs: left_term.into(),
                        rhs: original_right.into(),
                    },
                    left_vt,
                )
            } else {
                let (right_term, right_vt) =
                    term_replacement(original_right.clone(), taken_vars.clone(), true, false);
                if right_vt.is_some() {
                    (
                        Term::BinaryOperation {
                            op,
                            lhs: original_left.into(),
                            rhs: right_term.into(),
                        },
                        right_vt,
                    )
                } else {
                    // lhs and rhs did not contain abnormalities
                    // abnormal term, case b
                    if !op.definite() && !rhs_of_numeric_equation {
                        let v = Variable(taken_vars.choose_fresh_variable("V"));
                        let v_equals_t = Comparison {
                            relation: Relation::Equal,
                            lhs: Term::Variable(v.clone()),
                            rhs: Term::BinaryOperation {
                                op,
                                lhs: original_left.into(),
                                rhs: original_right.into(),
                            },
                        };
                        (Term::Variable(v), Some(v_equals_t))
                    } else {
                        (
                            Term::BinaryOperation {
                                op,
                                lhs: original_left.into(),
                                rhs: original_right.into(),
                            },
                            None,
                        )
                    }
                    // abnormal term, case a does not apply since op is the leading symbol
                }
            }
        }
    }
}

fn term_replacement_atom(atom: Atom, taken_vars: IndexSet<Variable>) -> (Atom, Option<Comparison>) {
    let mut v_equals_t = None;
    let mut new_terms = atom.terms.clone();
    for (i, term) in atom.terms.into_iter().enumerate() {
        let (current, vt) = term_replacement(term, taken_vars.clone(), false, false);
        if vt.is_some() {
            new_terms[i] = current;
            v_equals_t = vt;
            break;
        }
    }
    (
        Atom {
            predicate_symbol: atom.predicate_symbol,
            terms: new_terms,
        },
        v_equals_t,
    )
}

fn term_replacement_atomic_formula(
    formula: AtomicFormula,
    taken_vars: IndexSet<Variable>,
) -> (AtomicFormula, Option<Comparison>) {
    match formula {
        AtomicFormula::Literal(literal) => {
            let (atom, vt) = term_replacement_atom(literal.atom, taken_vars);
            (
                AtomicFormula::Literal(Literal {
                    sign: literal.sign,
                    atom,
                }),
                vt,
            )
        }

        AtomicFormula::Comparison(comparison) => {
            let numeric_equation = comparison.numeric_equation();
            let lhs = comparison.lhs;
            let rhs = comparison.rhs;

            let (left_term, vt) = term_replacement(lhs.clone(), taken_vars.clone(), false, false);
            if vt.is_some() {
                (
                    AtomicFormula::Comparison(Comparison {
                        relation: comparison.relation,
                        lhs: left_term,
                        rhs,
                    }),
                    vt,
                )
            } else {
                let (right_term, vt) =
                    term_replacement(rhs.clone(), taken_vars, false, numeric_equation);
                if vt.is_some() {
                    (
                        AtomicFormula::Comparison(Comparison {
                            relation: comparison.relation,
                            lhs,
                            rhs: right_term,
                        }),
                        vt,
                    )
                } else {
                    (
                        AtomicFormula::Comparison(Comparison {
                            relation: comparison.relation,
                            lhs,
                            rhs,
                        }),
                        None,
                    )
                }
            }
        }
    }
}

fn term_replacement_rule(rule: Rule) -> Rule {
    let taken_vars = rule.variables();
    let previous_head = rule.head.clone();

    // check head for abnormalities
    let (head, mut v_equals_t) = match rule.head {
        Head::Basic(atom) => {
            let (new_atom, v_equals_t) = term_replacement_atom(atom, taken_vars.clone());
            (Head::Basic(new_atom), v_equals_t)
        }
        Head::Choice(atom) => {
            let (new_atom, v_equals_t) = term_replacement_atom(atom, taken_vars.clone());
            (Head::Choice(new_atom), v_equals_t)
        }
        Head::Falsity => (Head::Falsity, None),
    };

    let mut body_literals = rule.body.formulas.clone();

    // if the head has not changed, check body for abnormalities
    if head == previous_head {
        for (i, formula) in rule.body.formulas.into_iter().enumerate() {
            let (new_formula, vt) = term_replacement_atomic_formula(formula, taken_vars.clone());
            if vt.is_some() {
                body_literals[i] = new_formula;
                v_equals_t = vt;
                break;
            }
        }
    }

    if let Some(formula) = v_equals_t {
        body_literals.push(AtomicFormula::Comparison(formula));
    }

    Rule {
        head,
        body: Body {
            formulas: body_literals,
        },
    }
}

// {H} :- Body
//   ==>
// H :- Body, not not H
fn normalize_choice_rule(rule: Rule) -> Rule {
    let head = rule.head.clone();
    match head {
        Head::Basic(_) | Head::Falsity => rule,
        Head::Choice(atom) => {
            let new_head = Head::Basic(atom.clone());
            let mut formulas = rule.body.formulas;
            formulas.push(AtomicFormula::Literal(Literal {
                sign: Sign::DoubleNegation,
                atom,
            }));
            Rule {
                head: new_head,
                body: Body { formulas },
            }
        }
    }
}

// innermost term replacement can occur in any order
// so, remove abnormalities in the head, then the body constructs (DFS)
// apply procedure until rule stops changing
pub(crate) fn numeric_normal_form_rule(rule: Rule) -> Rule {
    let mut previous = rule;
    let mut current = term_replacement_rule(previous.clone());

    while previous != current {
        previous = current;
        current = term_replacement_rule(previous.clone());
    }

    normalize_choice_rule(current)
}

pub fn numeric_normal_form(program: Program) -> Program {
    Program {
        rules: program
            .rules
            .into_iter()
            .map(numeric_normal_form_rule)
            .collect(),
    }
}

#[cfg(test)]
mod tests {

    use {
        super::{numeric_normal_form_rule, term_replacement, term_replacement_atomic_formula},
        crate::syntax_tree::asp::mini_gringo::Comparison,
        indexmap::IndexSet,
    };

    #[test]
    fn test_term_replacement() {
        for (term, scope, rhs, target) in [
            // base cases
            ("X+1", false, false, "X+1"),
            ("4-1", false, false, "4-1"),
            ("1*inf", false, false, "1*V1"),
            ("10+sup", false, false, "10+V1"),
            ("a+1", false, false, "V1+1"),
            ("X", false, false, "X"),
            ("X", true, false, "X"),
            ("a", false, false, "a"),
            ("a", true, false, "V1"),
            ("1", false, false, "1"),
            ("1", true, false, "1"),
            ("1/0", false, false, "V1"),
            ("1/0", false, true, "1/0"),
            // constructors
            ("f(a)", false, false, "f(a)"),
            ("f(a)", true, false, "V1"),
            ("f(X,Y+1)", false, false, "f(X,Y+1)"),
            ("f(X,a+1)", false, false, "f(X,V1+1)"),
            // unary op
            ("-(X+1)", false, false, "-(X+1)"),
            ("-(4-1)", false, false, "-(4-1)"),
            ("-(1*inf)", false, false, "-(1*V1)"),
            ("-(10+sup)", false, false, "-(10+V1)"),
            ("-(a+1)", false, false, "-(V1+1)"),
            ("-X", false, false, "-X"),
            ("-X", true, false, "-X"),
            ("-a", false, false, "-V1"),
            ("-a", true, false, "-V1"),
            ("-1", false, false, "-1"),
            ("-1", true, false, "-1"),
            ("-(1/0)", false, false, "-V1"),
            ("-(1/0)", false, true, "-V1"),
            // binop
            ("4-(X+1)", false, false, "4-(X+1)"),
            ("4-(a+1)", false, false, "4-(V1+1)"),
            ("4-(X+1)", true, false, "4-(X+1)"),
            ("4-(a+1)", true, false, "4-(V1+1)"),
            ("4+f(a)", false, false, "4+V1"),
            ("(4*a)-(a+1)", false, false, "(4*V1)-(a+1)"),
            ("((4*(1-a))+b)-(a+1)", false, false, "((4*(1-V1))+b)-(a+1)"),
        ] {
            let (src, _) = term_replacement(term.parse().unwrap(), IndexSet::new(), scope, rhs);
            let target = target.parse().unwrap();
            assert_eq!(src, target, "\n{src} \n!= \n{target}")
        }
    }

    #[test]
    fn test_term_replacement_atomic_formula() {
        for (src, target, vt) in [
            ("p(1..8)", "p(V1)", "V1 = 1..8"),
            ("X < a+1", "X < V1 + 1", "V1 = a"),
            ("X+1 < 3/5", "X+1 < V1", "V1 = 3/5"),
        ] {
            let (src, v_equals_t) =
                term_replacement_atomic_formula(src.parse().unwrap(), IndexSet::new());
            let target = target.parse().unwrap();
            let vt: Comparison = vt.parse().unwrap();
            assert_eq!(src, target, "\n{src} \n!= \n{target}");
            assert_eq!(v_equals_t, Some(vt));
        }

        for (src, target) in [("p(X+1)", "p(X+1)"), ("X+1 = 3/5", "X+1 = 3/5")] {
            let (src, v_equals_t) =
                term_replacement_atomic_formula(src.parse().unwrap(), IndexSet::new());
            let target = target.parse().unwrap();
            assert_eq!(src, target, "\n{src} \n!= \n{target}");
            assert_eq!(v_equals_t, None);
        }
    }

    #[test]
    fn test_numeric_normal_form_rule() {
        for (src, target) in [
            ("p(1..8).", "p(V1) :- V1 = 1..8."),
            ("{p(1..8)}.", "p(V1) :- V1 = 1..8, not not p(V1)."),
            ("{r} :- t.", "r :- t, not not r."),
            ("p(X/Y+1) :- q(X,Y).", "p(V1+1) :- q(X,Y), V1 = X/Y."),
            (
                "q(1..(X/2)) :- p(X).",
                "q(V2) :- p(X), V1 = X/2, V2 = 1..V1.",
            ),
            (
                "{q(1..8)} :- 4 = 1/X, p((1+a)..5).",
                "q(V1) :- 4 = 1/X, p(V3), V1 = 1..8, V2 = a, V3 = 1+V2..5, not not q(V1).",
            ),
            (
                ":- 1/Y = 4, p(Y), q(Y/5).",
                ":- V1 = 4, p(Y), q(V2), V1 = 1/Y, V2 = Y/5.",
            ),
            (
                ":- not p(0, f(a, X+1, b-3)).",
                ":- not p(0, f(a, X+1, V1-3)), V1 = b.",
            ),
        ] {
            let src = numeric_normal_form_rule(src.parse().unwrap());
            let target = target.parse().unwrap();
            assert_eq!(src, target, "\n{src} \n!= \n{target}")
        }
    }
}
