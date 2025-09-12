use {
    crate::{
        formatting::{Associativity, Precedence},
        syntax_tree::{
            Node,
            asp::mini_gringo::{
                Atom, AtomicFormula, BinaryOperator, Body, Comparison, Head, Literal,
                PrecomputedTerm, Predicate, Program, Relation, Rule, Sign, Term, UnaryOperator,
                Variable,
            },
        },
    },
    std::fmt::{self, Display, Formatter},
};

pub struct Format<'a, N: Node>(pub &'a N);

impl Display for Format<'_, PrecomputedTerm> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self.0 {
            PrecomputedTerm::Infimum => write!(f, "#inf"),
            PrecomputedTerm::Numeral(n) => write!(f, "{n}"),
            PrecomputedTerm::Symbol(s) => write!(f, "{s}"),
            PrecomputedTerm::Supremum => write!(f, "#sup"),
        }
    }
}

impl Display for Format<'_, Variable> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0.0)
    }
}

impl Display for Format<'_, UnaryOperator> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self.0 {
            UnaryOperator::Negative => write!(f, "-"),
        }
    }
}

impl Display for Format<'_, BinaryOperator> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self.0 {
            BinaryOperator::Add => write!(f, "+"),
            BinaryOperator::Subtract => write!(f, "-"),
            BinaryOperator::Multiply => write!(f, "*"),
            BinaryOperator::Divide => write!(f, "/"),
            BinaryOperator::Modulo => write!(f, "\\"),
            BinaryOperator::Interval => write!(f, ".."),
        }
    }
}

impl Precedence for Format<'_, Term> {
    fn precedence(&self) -> usize {
        match self.0 {
            Term::PrecomputedTerm(PrecomputedTerm::Numeral(1..)) => 1,
            Term::UnaryOperation {
                op: UnaryOperator::Negative,
                ..
            }
            | Term::PrecomputedTerm(_)
            | Term::Variable(_) => 0,
            Term::BinaryOperation {
                op: BinaryOperator::Multiply | BinaryOperator::Divide | BinaryOperator::Modulo,
                ..
            } => 2,
            Term::BinaryOperation {
                op: BinaryOperator::Add | BinaryOperator::Subtract,
                ..
            } => 3,
            Term::BinaryOperation {
                op: BinaryOperator::Interval,
                ..
            } => 4,
        }
    }

    fn associativity(&self) -> Associativity {
        Associativity::Left
    }

    fn fmt_operator(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self.0 {
            Term::UnaryOperation { op, .. } => write!(f, "{}", Format(op)),
            Term::BinaryOperation { op, .. } => match op {
                BinaryOperator::Interval => write!(f, "{}", Format(op)),
                _ => write!(f, " {} ", Format(op)),
            },
            Term::PrecomputedTerm(_) | Term::Variable(_) => unreachable!(),
        }
    }
}

impl Display for Format<'_, Term> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self.0 {
            Term::PrecomputedTerm(c) => Format(c).fmt(f),
            Term::Variable(v) => Format(v).fmt(f),
            Term::UnaryOperation { arg, .. } => self.fmt_unary(Format(arg.as_ref()), f),
            Term::BinaryOperation { lhs, rhs, .. } => {
                self.fmt_binary(Format(lhs.as_ref()), Format(rhs.as_ref()), f)
            }
        }
    }
}

impl Display for Format<'_, Predicate> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let symbol = &self.0.symbol;
        let arity = &self.0.arity;
        write!(f, "{symbol}/{arity}")
    }
}

impl Display for Format<'_, Atom> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let predicate = &self.0.predicate_symbol;
        let terms = &self.0.terms;

        write!(f, "{predicate}")?;

        if !terms.is_empty() {
            let mut iter = terms.iter().map(Format);
            write!(f, "({}", iter.next().unwrap())?;
            for term in iter {
                write!(f, ", {term}")?;
            }
            write!(f, ")")?;
        }

        Ok(())
    }
}

impl Display for Format<'_, Program> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        for rule in &self.0.rules {
            writeln!(f, "{}", Format(rule))?;
        }
        Ok(())
    }
}

impl Display for Format<'_, Sign> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self.0 {
            Sign::NoSign => write!(f, ""),
            Sign::Negation => write!(f, "not"),
            Sign::DoubleNegation => write!(f, "not not"),
        }
    }
}

impl Display for Format<'_, Literal> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        if self.0.sign == Sign::NoSign {
            write!(f, "{}", Format(&self.0.atom))
        } else {
            write!(f, "{} {}", Format(&self.0.sign), Format(&self.0.atom))
        }
    }
}

impl Display for Format<'_, Relation> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self.0 {
            Relation::Equal => write!(f, "="),
            Relation::NotEqual => write!(f, "!="),
            Relation::Less => write!(f, "<"),
            Relation::LessEqual => write!(f, "<="),
            Relation::Greater => write!(f, ">"),
            Relation::GreaterEqual => write!(f, ">="),
        }
    }
}

impl Display for Format<'_, Comparison> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{} {} {}",
            Format(&self.0.lhs),
            Format(&self.0.relation),
            Format(&self.0.rhs)
        )
    }
}

impl Display for Format<'_, AtomicFormula> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self.0 {
            AtomicFormula::Literal(l) => write!(f, "{}", Format(l)),
            AtomicFormula::Comparison(c) => write!(f, "{}", Format(c)),
        }
    }
}

impl Display for Format<'_, Head> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self.0 {
            Head::Basic(a) => write!(f, "{}", Format(a)),
            Head::Choice(a) => write!(f, "{{{}}}", Format(a)),
            Head::Falsity => write!(f, ""),
        }
    }
}

impl Display for Format<'_, Body> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let mut iter = self.0.formulas.iter().map(Format);
        if let Some(formula) = iter.next() {
            write!(f, "{formula}")?;
            for formula in iter {
                write!(f, ", {formula}")?;
            }
        }
        Ok(())
    }
}

impl Display for Format<'_, Rule> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{}", Format(&self.0.head))?;
        if self.0.head == Head::Falsity || !self.0.body.formulas.is_empty() {
            write!(f, " :- ")?;
        }
        write!(f, "{}.", Format(&self.0.body))
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        formatting::asp::default::Format,
        syntax_tree::asp::mini_gringo::{
            Atom, AtomicFormula, BinaryOperator, Body, Comparison, Head, Literal, PrecomputedTerm,
            Program, Relation, Rule, Sign, Term, UnaryOperator, Variable,
        },
    };

    #[test]
    fn format_precomputed_term() {
        assert_eq!(Format(&PrecomputedTerm::Infimum).to_string(), "#inf");
        assert_eq!(Format(&PrecomputedTerm::Numeral(-1)).to_string(), "-1");
        assert_eq!(Format(&PrecomputedTerm::Numeral(0)).to_string(), "0");
        assert_eq!(Format(&PrecomputedTerm::Numeral(42)).to_string(), "42");
        assert_eq!(
            Format(&PrecomputedTerm::Symbol("a".into())).to_string(),
            "a"
        );
        assert_eq!(Format(&PrecomputedTerm::Supremum).to_string(), "#sup");
    }

    #[test]
    fn format_variable() {
        assert_eq!(Format(&Variable("A".into())).to_string(), "A");
    }

    #[test]
    fn format_unary_operator() {
        assert_eq!(Format(&UnaryOperator::Negative).to_string(), "-");
    }

    #[test]
    fn format_binary_operator() {
        assert_eq!(Format(&BinaryOperator::Add).to_string(), "+");
        assert_eq!(Format(&BinaryOperator::Subtract).to_string(), "-");
        assert_eq!(Format(&BinaryOperator::Multiply).to_string(), "*");
        assert_eq!(Format(&BinaryOperator::Divide).to_string(), "/");
        assert_eq!(Format(&BinaryOperator::Modulo).to_string(), "\\");
        assert_eq!(Format(&BinaryOperator::Interval).to_string(), "..");
    }

    #[test]
    fn format_term() {
        assert_eq!(
            Format(&Term::PrecomputedTerm(PrecomputedTerm::Numeral(42))).to_string(),
            "42"
        );

        assert_eq!(
            Format(&Term::Variable(Variable("A".into()))).to_string(),
            "A"
        );

        assert_eq!(
            Format(&Term::BinaryOperation {
                op: BinaryOperator::Add,
                lhs: Term::PrecomputedTerm(PrecomputedTerm::Numeral(1)).into(),
                rhs: Term::BinaryOperation {
                    op: BinaryOperator::Multiply,
                    lhs: Term::PrecomputedTerm(PrecomputedTerm::Numeral(2)).into(),
                    rhs: Term::PrecomputedTerm(PrecomputedTerm::Numeral(3)).into(),
                }
                .into(),
            })
            .to_string(),
            "1 + 2 * 3"
        );

        assert_eq!(
            Format(&Term::BinaryOperation {
                op: BinaryOperator::Multiply,
                lhs: Term::PrecomputedTerm(PrecomputedTerm::Numeral(1)).into(),
                rhs: Term::BinaryOperation {
                    op: BinaryOperator::Add,
                    lhs: Term::PrecomputedTerm(PrecomputedTerm::Numeral(2)).into(),
                    rhs: Term::PrecomputedTerm(PrecomputedTerm::Numeral(3)).into(),
                }
                .into(),
            })
            .to_string(),
            "1 * (2 + 3)"
        );

        assert_eq!(
            Format(&Term::BinaryOperation {
                op: BinaryOperator::Add,
                lhs: Term::PrecomputedTerm(PrecomputedTerm::Numeral(1)).into(),
                rhs: Term::BinaryOperation {
                    op: BinaryOperator::Add,
                    lhs: Term::PrecomputedTerm(PrecomputedTerm::Numeral(2)).into(),
                    rhs: Term::PrecomputedTerm(PrecomputedTerm::Numeral(3)).into(),
                }
                .into(),
            })
            .to_string(),
            "1 + (2 + 3)"
        );

        assert_eq!(
            Format(&Term::BinaryOperation {
                op: BinaryOperator::Add,
                lhs: Term::BinaryOperation {
                    op: BinaryOperator::Add,
                    lhs: Term::PrecomputedTerm(PrecomputedTerm::Numeral(1)).into(),
                    rhs: Term::PrecomputedTerm(PrecomputedTerm::Numeral(2)).into(),
                }
                .into(),
                rhs: Term::PrecomputedTerm(PrecomputedTerm::Numeral(3)).into(),
            })
            .to_string(),
            "1 + 2 + 3"
        );
    }

    #[test]
    fn format_atom() {
        assert_eq!(
            Format(&Atom {
                predicate_symbol: "p".into(),
                terms: vec![],
            })
            .to_string(),
            "p"
        );

        assert_eq!(
            Format(&Atom {
                predicate_symbol: "p".into(),
                terms: vec![Term::PrecomputedTerm(PrecomputedTerm::Numeral(1))],
            })
            .to_string(),
            "p(1)"
        );

        assert_eq!(
            Format(&Atom {
                predicate_symbol: "p".into(),
                terms: vec![
                    Term::PrecomputedTerm(PrecomputedTerm::Numeral(1)),
                    Term::PrecomputedTerm(PrecomputedTerm::Numeral(2))
                ],
            })
            .to_string(),
            "p(1, 2)"
        );
    }

    #[test]
    fn format_sign() {
        assert_eq!(Format(&Sign::NoSign).to_string(), "");
        assert_eq!(Format(&Sign::Negation).to_string(), "not");
        assert_eq!(Format(&Sign::DoubleNegation).to_string(), "not not");
    }

    #[test]
    fn format_literal() {
        assert_eq!(
            Format(&Literal {
                sign: Sign::Negation,
                atom: Atom {
                    predicate_symbol: "p".into(),
                    terms: vec![]
                }
            })
            .to_string(),
            "not p"
        );
    }

    #[test]
    fn format_relation() {
        assert_eq!(Format(&Relation::Equal).to_string(), "=");
        assert_eq!(Format(&Relation::NotEqual).to_string(), "!=");
        assert_eq!(Format(&Relation::Less).to_string(), "<");
        assert_eq!(Format(&Relation::LessEqual).to_string(), "<=");
        assert_eq!(Format(&Relation::Greater).to_string(), ">");
        assert_eq!(Format(&Relation::GreaterEqual).to_string(), ">=");
    }

    #[test]
    fn format_comparison() {
        assert_eq!(
            Format(&Comparison {
                relation: Relation::Equal,
                lhs: Term::Variable(Variable("I".into())),
                rhs: Term::PrecomputedTerm(PrecomputedTerm::Numeral(1))
            })
            .to_string(),
            "I = 1"
        );
    }

    #[test]
    fn format_atomic_formula() {
        assert_eq!(
            Format(&AtomicFormula::Literal(Literal {
                sign: Sign::DoubleNegation,
                atom: Atom {
                    predicate_symbol: "p".into(),
                    terms: vec![]
                }
            }))
            .to_string(),
            "not not p"
        );

        assert_eq!(
            Format(&AtomicFormula::Comparison(Comparison {
                relation: Relation::NotEqual,
                lhs: Term::PrecomputedTerm(PrecomputedTerm::Numeral(1)),
                rhs: Term::PrecomputedTerm(PrecomputedTerm::Numeral(2))
            }))
            .to_string(),
            "1 != 2"
        );
    }

    #[test]
    fn format_head() {
        assert_eq!(
            Format(&Head::Basic(Atom {
                predicate_symbol: "p".into(),
                terms: vec![]
            }))
            .to_string(),
            "p"
        );

        assert_eq!(
            Format(&Head::Choice(Atom {
                predicate_symbol: "p".into(),
                terms: vec![]
            }))
            .to_string(),
            "{p}"
        );

        assert_eq!(Format(&Head::Falsity).to_string(), "");
    }

    #[test]
    fn format_body() {
        assert_eq!(Format(&Body { formulas: vec![] }).to_string(), "");

        assert_eq!(
            Format(&Body {
                formulas: vec![
                    AtomicFormula::Literal(Literal {
                        sign: Sign::NoSign,
                        atom: Atom {
                            predicate_symbol: "p".into(),
                            terms: vec![Term::Variable(Variable("X".into()))]
                        }
                    }),
                    AtomicFormula::Comparison(Comparison {
                        relation: Relation::Less,
                        lhs: Term::Variable(Variable("X".into())),
                        rhs: Term::PrecomputedTerm(PrecomputedTerm::Numeral(10))
                    })
                ]
            })
            .to_string(),
            "p(X), X < 10"
        );
    }

    #[test]
    fn format_rule() {
        // TODO
    }

    #[test]
    fn format_program() {
        assert_eq!(
            Format(&Program {
                rules: vec![
                    Rule {
                        head: Head::Basic(Atom {
                            predicate_symbol: "a".into(),
                            terms: vec![]
                        }),
                        body: Body { formulas: vec![] }
                    },
                    Rule {
                        head: Head::Basic(Atom {
                            predicate_symbol: "b".into(),
                            terms: vec![]
                        }),
                        body: Body {
                            formulas: vec![AtomicFormula::Literal(Literal {
                                sign: Sign::Negation,
                                atom: Atom {
                                    predicate_symbol: "a".into(),
                                    terms: vec![]
                                }
                            })]
                        }
                    }
                ]
            })
            .to_string(),
            "a.\nb :- not a.\n"
        );
    }
}
