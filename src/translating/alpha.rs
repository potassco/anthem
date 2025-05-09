// superasp -> asp reduction

use std::fmt::Display;

use crate::syntax_tree::{asp, superasp};
use thiserror::Error;

impl From<superasp::PrecomputedTerm> for asp::PrecomputedTerm {
    fn from(value: superasp::PrecomputedTerm) -> Self {
        format!("{value}").parse().unwrap()
    }
}

impl From<superasp::Variable> for asp::Variable {
    fn from(value: superasp::Variable) -> Self {
        format!("{value}").parse().unwrap()
    }
}

impl From<superasp::UnaryOperator> for asp::UnaryOperator {
    fn from(value: superasp::UnaryOperator) -> Self {
        format!("{value}").parse().unwrap()
    }
}

impl From<superasp::BinaryOperator> for asp::BinaryOperator {
    fn from(value: superasp::BinaryOperator) -> Self {
        format!("{value}").parse().unwrap()
    }
}

impl From<superasp::Term> for asp::Term {
    fn from(value: superasp::Term) -> Self {
        format!("{value}").parse().unwrap()
    }
}

impl From<superasp::Predicate> for asp::Predicate {
    fn from(value: superasp::Predicate) -> Self {
        format!("{value}").parse().unwrap()
    }
}

impl From<superasp::Atom> for asp::Atom {
    fn from(value: superasp::Atom) -> Self {
        format!("{value}").parse().unwrap()
    }
}

impl From<superasp::Sign> for asp::Sign {
    fn from(value: superasp::Sign) -> Self {
        format!("{value}").parse().unwrap()
    }
}

impl From<superasp::Literal> for asp::Literal {
    fn from(value: superasp::Literal) -> Self {
        format!("{value}").parse().unwrap()
    }
}

impl From<superasp::Relation> for asp::Relation {
    fn from(value: superasp::Relation) -> Self {
        format!("{value}").parse().unwrap()
    }
}

impl From<superasp::Comparison> for asp::Comparison {
    fn from(value: superasp::Comparison) -> Self {
        format!("{value}").parse().unwrap()
    }
}

impl From<superasp::AtomicFormula> for asp::AtomicFormula {
    fn from(value: superasp::AtomicFormula) -> Self {
        format!("{value}").parse().unwrap()
    }
}

impl From<superasp::AggregateOperation> for asp::AggregateOperation {
    fn from(value: superasp::AggregateOperation) -> Self {
        match value {
            superasp::AggregateOperation::Count => asp::AggregateOperation::Count,
        }
    }
}

impl From<superasp::Aggregate> for asp::Aggregate {
    fn from(value: superasp::Aggregate) -> Self {
        format!("{value}").parse().unwrap()
    }
}

impl From<superasp::AggregateOrder> for asp::AggregateOrder {
    fn from(value: superasp::AggregateOrder) -> Self {
        match value {
            superasp::AggregateOrder::Left => asp::AggregateOrder::Left,
            superasp::AggregateOrder::Right => asp::AggregateOrder::Right,
        }
    }
}

#[derive(Error, Debug)]
pub enum AlphaTranslationError {
    UnsupportedLanguageFeature(superasp::AggregateAtom),
}

impl Display for AlphaTranslationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            AlphaTranslationError::UnsupportedLanguageFeature(atom) => {
                writeln!(f, "the atom `{atom}` is not mgc compliant")
            }
        }
    }
}

fn alpha_aggregate_atom(
    atom: superasp::AggregateAtom,
) -> Result<Vec<asp::AggregateAtom>, AlphaTranslationError> {
    let mut atoms = vec![];
    match atom.relation {
        superasp::Relation::Equal => {
            atoms.push(asp::AggregateAtom {
                aggregate: atom.aggregate.clone().into(),
                relation: asp::Relation::LessEqual,
                guard: atom.guard.clone().into(),
                order: atom.order.into(),
            });
            atoms.push(asp::AggregateAtom {
                aggregate: atom.aggregate.into(),
                relation: asp::Relation::GreaterEqual,
                guard: atom.guard.into(),
                order: atom.order.into(),
            });
        }
        superasp::Relation::LessEqual => {
            atoms.push(asp::AggregateAtom {
                aggregate: atom.aggregate.into(),
                relation: asp::Relation::LessEqual,
                guard: atom.guard.into(),
                order: atom.order.into(),
            });
        }
        superasp::Relation::GreaterEqual => {
            atoms.push(asp::AggregateAtom {
                aggregate: atom.aggregate.into(),
                relation: asp::Relation::GreaterEqual,
                guard: atom.guard.into(),
                order: atom.order.into(),
            });
        }
        _ => return Err(AlphaTranslationError::UnsupportedLanguageFeature(atom)),
    }

    Ok(atoms)
}

fn alpha_rule_body(body: superasp::Body) -> Result<asp::Body, AlphaTranslationError> {
    let mut body_literals: Vec<asp::BodyLiteral> = vec![];
    for literal in body.literals {
        match literal {
            superasp::BodyLiteral::AtomicFormula(formula) => {
                let f: asp::AtomicFormula = formula.into();
                body_literals.push(asp::BodyLiteral::AtomicFormula(f))
            }
            superasp::BodyLiteral::AggregateAtom(atom) => {
                let atoms = alpha_aggregate_atom(atom)?;
                for a in atoms {
                    body_literals.push(asp::BodyLiteral::AggregateAtom(a));
                }
            }
        }
    }

    Ok(asp::Body {
        literals: body_literals,
    })
}

fn alpha_rule(rule: superasp::Rule) -> Result<Vec<asp::Rule>, AlphaTranslationError> {
    let mut rules = vec![];
    let body = alpha_rule_body(rule.body.clone())?;

    match rule.head {
        superasp::Head::Basic(atom) => {
            rules.push(asp::Rule {
                head: asp::Head::Basic(atom.into()),
                body,
            });
        }
        superasp::Head::Choice(atom) => {
            rules.push(asp::Rule {
                head: asp::Head::Choice(atom.into()),
                body,
            });
        }
        superasp::Head::Falsity => {
            rules.push(asp::Rule {
                head: asp::Head::Falsity,
                body,
            });
        }
        superasp::Head::ChoiceWithBounds(head) => {
            // {A} :- Body
            rules.push(asp::Rule {
                head: asp::Head::Choice(head.atom.clone().into()),
                body,
            });

            // count{ X : A }
            let aggregate = superasp::Aggregate {
                operation: superasp::AggregateOperation::Count,
                variable_list: head.variables,
                conditions: vec![superasp::AtomicFormula::Literal(superasp::Literal {
                    sign: superasp::Sign::NoSign,
                    atom: head.atom,
                })],
            };

            // :- Body, count{ X : A } <= m-1
            if let Some(m) = head.lower {
                let mut extended_literals = rule.body.literals.clone();
                extended_literals.push(superasp::BodyLiteral::AggregateAtom(
                    superasp::AggregateAtom {
                        aggregate: aggregate.clone(),
                        relation: superasp::Relation::LessEqual,
                        guard: superasp::Term::PrecomputedTerm(superasp::PrecomputedTerm::Numeral(
                            m - 1,
                        )),
                        order: superasp::AggregateOrder::Left,
                    },
                ));
                let extended_body = superasp::Body {
                    literals: extended_literals,
                };
                rules.push(asp::Rule {
                    head: asp::Head::Falsity,
                    body: alpha_rule_body(extended_body)?,
                });
            }

            // :- Body, count{ X : A } >= n+1
            if let Some(n) = head.upper {
                let mut extended_literals = rule.body.literals;
                extended_literals.push(superasp::BodyLiteral::AggregateAtom(
                    superasp::AggregateAtom {
                        aggregate,
                        relation: superasp::Relation::GreaterEqual,
                        guard: superasp::Term::PrecomputedTerm(superasp::PrecomputedTerm::Numeral(
                            n + 1,
                        )),
                        order: superasp::AggregateOrder::Left,
                    },
                ));
                let extended_body = superasp::Body {
                    literals: extended_literals,
                };
                rules.push(asp::Rule {
                    head: asp::Head::Falsity,
                    body: alpha_rule_body(extended_body)?,
                });
            }
        }
    }

    Ok(rules)
}

pub fn alpha(program: superasp::Program) -> Result<asp::Program, AlphaTranslationError> {
    let mut rules = vec![];

    for superrule in program {
        let rule_vec = alpha_rule(superrule)?;
        rules.extend(rule_vec);
    }

    Ok(asp::Program { rules })
}

#[cfg(test)]
mod tests {

    use crate::syntax_tree::{asp, superasp};

    use super::alpha;

    #[test]
    fn test_precomputed_term() {
        let src: asp::PrecomputedTerm = superasp::PrecomputedTerm::Numeral(5).into();
        let target = asp::PrecomputedTerm::Numeral(5);

        assert_eq!(src, target);
    }

    #[test]
    fn test_alpha_program() {
        for (src, target) in [
            ("p(X) :- q(X).", "p(X) :- q(X)."),
            (
                "p(Y) :- #count{ X : p(X,Y) } <= 5.",
                "p(Y) :- #count{ X : p(X,Y) } <= 5.",
            ),
            (
                "3 { X : p(X) } 5 :- q, t.",
                "{p(X)} :- q, t. :- q, t, #count{ X : p(X) } <= 2. :- q, t, #count{ X : p(X) } >= 6.",
            ),
            (
                "p(Y) :- #count{ X : p(X,Y) } = 5.",
                "p(Y) :- #count{ X : p(X,Y) } <= 5, #count{ X : p(X,Y) } >= 5.",
            ),
        ] {
            let right: asp::Program = target.parse().unwrap();
            let left = alpha(src.parse().unwrap()).unwrap();

            assert_eq!(left, right, "{left} \n!=\n {right}");
        }
    }
}
