use {
    crate::{
        formatting::{Associativity, Precedence},
        syntax_tree::{
            fol::{
                Atom, AtomicFormula, BinaryConnective, BinaryOperator, Comparison, Formula,
                FunctionConstant, GeneralTerm, IntegerTerm, Quantification, Quantifier, Relation,
                Sort, SymbolicTerm, UnaryConnective, UnaryOperator, Variable,
            },
            Node,
        },
    },
    std::fmt::{self, Display, Formatter},
};

pub struct Format<'a, N: Node>(pub &'a N);

impl Display for Format<'_, UnaryOperator> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self.0 {
            UnaryOperator::Negative => write!(f, "$uminus"),
        }
    }
}

impl Display for Format<'_, BinaryOperator> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self.0 {
            BinaryOperator::Add => write!(f, "$sum"),
            BinaryOperator::Subtract => write!(f, "$difference"),
            BinaryOperator::Multiply => write!(f, "$product"),
        }
    }
}

impl Display for Format<'_, IntegerTerm> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self.0 {
            IntegerTerm::Numeral(n) => {
                if *n < 0 {
                    let m = n.abs();
                    write!(f, "$uminus({m})")?;
                } else {
                    write!(f, "{n}")?;
                }

                Ok(())
            }
            IntegerTerm::Variable(v) => write!(f, "{v}_i"),
            IntegerTerm::FunctionConstant(c) => write!(f, "{c}_i"),
            IntegerTerm::UnaryOperation { op, arg } => {
                let op = Format(op);
                let arg = Format(arg.as_ref());
                write!(f, "{op}({arg})")
            }
            IntegerTerm::BinaryOperation { op, lhs, rhs } => {
                let op = Format(op);
                let lhs = Format(lhs.as_ref());
                let rhs = Format(rhs.as_ref());
                write!(f, "{op}({lhs}, {rhs})")
            }
        }
    }
}

impl Display for Format<'_, SymbolicTerm> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self.0 {
            SymbolicTerm::Symbol(s) => write!(f, "{s}"),
            SymbolicTerm::FunctionConstant(c) => write!(f, "{c}_s"),
            SymbolicTerm::Variable(v) => write!(f, "{v}_s"),
        }
    }
}

impl Display for Format<'_, GeneralTerm> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self.0 {
            GeneralTerm::Infimum => write!(f, "c__infimum__"),
            GeneralTerm::Supremum => write!(f, "c__supremum__"),
            GeneralTerm::FunctionConstant(c) => write!(f, "{c}_g"),
            GeneralTerm::Variable(v) => write!(f, "{v}_g"),
            GeneralTerm::IntegerTerm(t) => write!(f, "f__integer__({})", Format(t)),
            GeneralTerm::SymbolicTerm(t) => write!(f, "f__symbolic__({})", Format(t)),
        }
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

impl Format<'_, Relation> {
    fn repr_integer(&self) -> &'static str {
        match self.0 {
            Relation::Equal => "=",
            Relation::NotEqual => "!=",
            Relation::GreaterEqual => "$greatereq",
            Relation::LessEqual => "$lesseq",
            Relation::Greater => "$greater",
            Relation::Less => "$less",
        }
    }

    fn repr_general(&self) -> &'static str {
        match self.0 {
            Relation::Equal => "=",
            Relation::NotEqual => "!=",
            Relation::GreaterEqual => "p__greater_equal__",
            Relation::LessEqual => "p__less_equal__",
            Relation::Greater => "p__greater__",
            Relation::Less => "p__less__",
        }
    }
}

impl Display for Format<'_, Relation> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.repr_general())
    }
}

impl Display for Format<'_, Comparison> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        for (counter, (lhs, relation, rhs)) in self.0.individuals().enumerate() {
            if counter > 0 {
                write!(f, " & ")?;
            }

            match (lhs, rhs) {
                (GeneralTerm::IntegerTerm(lhs), GeneralTerm::IntegerTerm(rhs)) => match relation {
                    Relation::Equal | Relation::NotEqual => write!(
                        f,
                        "{} {} {}",
                        Format(lhs),
                        Format(relation).repr_integer(),
                        Format(rhs)
                    ),
                    _ => write!(
                        f,
                        "{}({}, {})",
                        Format(relation).repr_integer(),
                        Format(lhs),
                        Format(rhs)
                    ),
                },

                (GeneralTerm::SymbolicTerm(lhs), GeneralTerm::SymbolicTerm(rhs))
                    if matches!(relation, Relation::Equal | Relation::NotEqual) =>
                {
                    write!(f, "{} {} {}", Format(lhs), Format(relation), Format(rhs))
                }

                (lhs, rhs) => match relation {
                    Relation::Equal | Relation::NotEqual => {
                        write!(f, "{} {} {}", Format(lhs), Format(relation), Format(rhs))
                    }
                    _ => write!(f, "{}({}, {})", Format(relation), Format(lhs), Format(rhs)),
                },
            }?;
        }

        Ok(())
    }
}

impl Display for Format<'_, AtomicFormula> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self.0 {
            AtomicFormula::Truth => write!(f, "$true"),
            AtomicFormula::Falsity => write!(f, "$false"),
            AtomicFormula::Atom(a) => Format(a).fmt(f),
            AtomicFormula::Comparison(c) => Format(c).fmt(f),
        }
    }
}

impl Display for Format<'_, Quantifier> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self.0 {
            Quantifier::Forall => write!(f, "!"),
            Quantifier::Exists => write!(f, "?"),
        }
    }
}

impl Display for Format<'_, FunctionConstant> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let name = &self.0.name;
        let sort = &self.0.sort;

        match sort {
            Sort::General => write!(f, "{name}_g"),
            Sort::Integer => write!(f, "{name}_i"),
            Sort::Symbol => write!(f, "{name}_s"),
        }
    }
}

impl Display for Format<'_, Variable> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let name = &self.0.name;
        let sort = &self.0.sort;

        match sort {
            Sort::General => write!(f, "{name}_g"),
            Sort::Integer => write!(f, "{name}_i"),
            Sort::Symbol => write!(f, "{name}_s"),
        }
    }
}

impl Display for Format<'_, Quantification> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let variables = &self.0.variables;

        write!(f, "{}[", Format(&self.0.quantifier))?;

        for (counter, var) in variables.iter().enumerate() {
            if counter > 0 {
                write!(f, ", ")?;
            }
            match var.sort {
                Sort::General => write!(f, "{}: general", Format(var)),
                Sort::Integer => write!(f, "{}: $int", Format(var)),
                Sort::Symbol => write!(f, "{}: symbol", Format(var)),
            }?;
        }

        write!(f, "]")?;

        Ok(())
    }
}

impl Display for Format<'_, UnaryConnective> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self.0 {
            UnaryConnective::Negation => write!(f, "~"),
        }
    }
}

impl Display for Format<'_, BinaryConnective> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self.0 {
            BinaryConnective::Equivalence => write!(f, "<=>"),
            BinaryConnective::Implication => write!(f, "=>"),
            BinaryConnective::ReverseImplication => write!(f, "<="),
            BinaryConnective::Conjunction => write!(f, "&"),
            BinaryConnective::Disjunction => write!(f, "|"),
        }
    }
}

impl Precedence for Format<'_, Formula> {
    fn precedence(&self) -> usize {
        match self.0 {
            Formula::AtomicFormula(_) => 0,
            Formula::UnaryFormula { .. } => 1,
            Formula::QuantifiedFormula { .. } => 2,
            Formula::BinaryFormula { .. } => 3,
        }
    }

    fn associativity(&self) -> Associativity {
        Associativity::Left
    }

    fn fmt_operator(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self.0 {
            Formula::UnaryFormula { connective, .. } => write!(f, "{}", Format(connective)),
            Formula::BinaryFormula { connective, .. } => write!(f, " {} ", Format(connective)),
            Formula::QuantifiedFormula { quantification, .. } => {
                write!(f, "{}: ", Format(quantification))
            }
            Formula::AtomicFormula(_) => unreachable!(),
        }
    }
}

impl Display for Format<'_, Formula> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self.0 {
            Formula::AtomicFormula(a) => Format(a).fmt(f),
            Formula::UnaryFormula { formula, .. } => self.fmt_unary(Format(formula.as_ref()), f),
            Formula::QuantifiedFormula {
                quantification,
                formula,
            } => {
                // no precedence formatting needed
                let connective = Format(quantification);
                let formula = Format(formula.as_ref());
                write!(f, "{connective}: ({formula})")
            }
            Formula::BinaryFormula { lhs, rhs, .. } => {
                self.fmt_binary(Format(lhs.as_ref()), Format(rhs.as_ref()), f)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        formatting::fol::tptp::Format,
        syntax_tree::fol::{
            Atom, AtomicFormula, BinaryConnective, BinaryOperator, Comparison, Formula,
            GeneralTerm, Guard, IntegerTerm, Quantification, Quantifier, Relation, Sort,
            SymbolicTerm, UnaryOperator, Variable,
        },
    };

    #[test]
    fn format_integer_term() {
        assert_eq!(Format(&IntegerTerm::Numeral(0)).to_string(), "0");
        assert_eq!(Format(&IntegerTerm::Numeral(42)).to_string(), "42");
        assert_eq!(
            Format(&IntegerTerm::Numeral(-42)).to_string(),
            "$uminus(42)"
        );
        assert_eq!(
            Format(&IntegerTerm::Variable("A".into())).to_string(),
            "A_i"
        );
        assert_eq!(
            Format(&IntegerTerm::BinaryOperation {
                op: BinaryOperator::Multiply,
                lhs: IntegerTerm::Numeral(1).into(),
                rhs: IntegerTerm::Numeral(5).into(),
            })
            .to_string(),
            "$product(1, 5)"
        );
        assert_eq!(
            Format(&IntegerTerm::BinaryOperation {
                op: BinaryOperator::Add,
                lhs: IntegerTerm::Numeral(10).into(),
                rhs: IntegerTerm::Variable("N".into()).into(),
            })
            .to_string(),
            "$sum(10, N_i)"
        );
        assert_eq!(
            Format(&IntegerTerm::BinaryOperation {
                op: BinaryOperator::Subtract,
                lhs: IntegerTerm::Numeral(-195).into(),
                rhs: IntegerTerm::UnaryOperation {
                    op: UnaryOperator::Negative,
                    arg: IntegerTerm::Variable("N".into()).into(),
                }
                .into(),
            })
            .to_string(),
            "$difference($uminus(195), $uminus(N_i))"
        );
    }

    #[test]
    fn format_symbolic_term() {
        assert_eq!(Format(&SymbolicTerm::Symbol("p".into())).to_string(), "p");
        assert_eq!(
            Format(&SymbolicTerm::Variable("X".into())).to_string(),
            "X_s"
        )
    }

    #[test]
    fn format_general_term() {
        assert_eq!(Format(&GeneralTerm::Infimum).to_string(), "c__infimum__");
        assert_eq!(Format(&GeneralTerm::Supremum).to_string(), "c__supremum__");
        assert_eq!(
            Format(&GeneralTerm::Variable("N1".into())).to_string(),
            "N1_g"
        );
        assert_eq!(
            Format(&GeneralTerm::SymbolicTerm(SymbolicTerm::Symbol("p".into()))).to_string(),
            "f__symbolic__(p)"
        );
        assert_eq!(
            Format(&GeneralTerm::IntegerTerm(IntegerTerm::Numeral(1))).to_string(),
            "f__integer__(1)"
        )
    }

    #[test]
    fn format_atom() {
        assert_eq!(
            Format(&Atom {
                predicate_symbol: "prime".into(),
                terms: vec![
                    GeneralTerm::IntegerTerm(IntegerTerm::BinaryOperation {
                        op: BinaryOperator::Add,
                        lhs: IntegerTerm::Variable("N1".into()).into(),
                        rhs: IntegerTerm::Numeral(3).into(),
                    }),
                    GeneralTerm::IntegerTerm(IntegerTerm::Numeral(5)),
                ]
            })
            .to_string(),
            "prime(f__integer__($sum(N1_i, 3)), f__integer__(5))"
        )
    }

    #[test]
    fn format_comparison() {
        assert_eq!(
            Format(&Comparison {
                term: GeneralTerm::IntegerTerm(IntegerTerm::Numeral(5)),
                guards: vec![Guard {
                    relation: Relation::Equal,
                    term: GeneralTerm::IntegerTerm(IntegerTerm::Numeral(3)),
                }]
            })
            .to_string(),
            // "f__integer__(5) = f__integer__(3)"
            "5 = 3"
        );
        assert_eq!(
            Format(&Comparison {
                term: GeneralTerm::IntegerTerm(IntegerTerm::Numeral(5)),
                guards: vec![Guard {
                    relation: Relation::NotEqual,
                    term: GeneralTerm::IntegerTerm(IntegerTerm::Numeral(3)),
                }]
            })
            .to_string(),
            // "f__integer__(5) != f__integer__(3)"
            "5 != 3"
        );
        assert_eq!(
            Format(&Comparison {
                term: GeneralTerm::IntegerTerm(IntegerTerm::Numeral(5)),
                guards: vec![Guard {
                    relation: Relation::LessEqual,
                    term: GeneralTerm::IntegerTerm(IntegerTerm::Numeral(3)),
                }]
            })
            .to_string(),
            // "p__less_equal__(f__integer__(5), f__integer__(3))"
            "$lesseq(5, 3)"
        );
        assert_eq!(
            Format(&Comparison {
                term: GeneralTerm::IntegerTerm(IntegerTerm::Numeral(5)),
                guards: vec![
                    Guard {
                        relation: Relation::LessEqual,
                        term: GeneralTerm::IntegerTerm(IntegerTerm::Numeral(3)),
                    },
                    Guard {
                        relation: Relation::Equal,
                        term: GeneralTerm::IntegerTerm(IntegerTerm::Numeral(4)),
                    }
                ]
            })
            .to_string(),
            // "p__less_equal__(f__integer__(5), f__integer__(3)) & f__integer__(3) = f__integer__(4)"
            "$lesseq(5, 3) & 3 = 4"
        );
        assert_eq!(
            Format(&Comparison {
                term: GeneralTerm::IntegerTerm(IntegerTerm::Numeral(5)),
                guards: vec![
                    Guard {
                        relation: Relation::LessEqual,
                        term: GeneralTerm::IntegerTerm(IntegerTerm::Numeral(3)),
                    },
                    Guard {
                        relation: Relation::Less,
                        term: GeneralTerm::IntegerTerm(IntegerTerm::Numeral(6)),
                    },
                    Guard {
                        relation: Relation::NotEqual,
                        term: GeneralTerm::IntegerTerm(IntegerTerm::Numeral(5)),
                    }
                ]
            })
            .to_string(),
            // "p__less_equal__(f__integer__(5), f__integer__(3)) & p__less__(f__integer__(3), f__integer__(6)) & f__integer__(6) != f__integer__(5)"
            "$lesseq(5, 3) & $less(3, 6) & 6 != 5"
        );
        assert_eq!(
            Format(&Comparison {
                term: GeneralTerm::IntegerTerm(IntegerTerm::Numeral(1)),
                guards: vec![
                    Guard {
                        relation: Relation::Less,
                        term: GeneralTerm::IntegerTerm(IntegerTerm::Numeral(2)),
                    },
                    Guard {
                        relation: Relation::Less,
                        term: GeneralTerm::Variable("X".to_string()),
                    },
                ]
            })
            .to_string(),
            "$less(1, 2) & p__less__(f__integer__(2), X_g)"
        );
        assert_eq!(
            Format(&Comparison {
                term: GeneralTerm::IntegerTerm(IntegerTerm::Numeral(1)),
                guards: vec![Guard {
                    relation: Relation::Less,
                    term: GeneralTerm::IntegerTerm(IntegerTerm::Variable("N".to_string())),
                },]
            })
            .to_string(),
            "$less(1, N_i)"
        );
        assert_eq!(
            Format(&Comparison {
                term: GeneralTerm::SymbolicTerm(SymbolicTerm::Symbol("a".to_string())),
                guards: vec![Guard {
                    relation: Relation::Equal,
                    term: GeneralTerm::SymbolicTerm(SymbolicTerm::Variable("B".to_string())),
                },]
            })
            .to_string(),
            // "f__symbolic__(a) = f__symbolic__(B$s)"
            "a = B_s"
        );
        assert_eq!(
            Format(&Comparison {
                term: GeneralTerm::SymbolicTerm(SymbolicTerm::Symbol("a".to_string())),
                guards: vec![Guard {
                    relation: Relation::Less,
                    term: GeneralTerm::SymbolicTerm(SymbolicTerm::Variable("B".to_string())),
                },]
            })
            .to_string(),
            "p__less__(f__symbolic__(a), f__symbolic__(B_s))"
        );
    }

    #[test]
    fn format_quantification() {
        assert_eq!(
            Format(&Quantification {
                quantifier: Quantifier::Forall,
                variables: vec![
                    Variable {
                        name: "X1".into(),
                        sort: Sort::Integer,
                    },
                    Variable {
                        name: "N2".into(),
                        sort: Sort::General,
                    },
                ]
            })
            .to_string(),
            "![X1_i: $int, N2_g: general]"
        );
        assert_eq!(
            Format(&Quantification {
                quantifier: Quantifier::Exists,
                variables: vec![Variable {
                    name: "X1".into(),
                    sort: Sort::Symbol,
                },]
            })
            .to_string(),
            "?[X1_s: symbol]"
        );
    }

    #[test]
    fn format_formula() {
        assert_eq!(
            Format(&Formula::AtomicFormula(AtomicFormula::Atom(Atom {
                predicate_symbol: "p".into(),
                terms: vec![]
            })))
            .to_string(),
            "p"
        );
        assert_eq!(
            Format(&Formula::BinaryFormula {
                connective: BinaryConnective::Implication,
                lhs: Formula::BinaryFormula {
                    connective: BinaryConnective::Implication,
                    lhs: Formula::AtomicFormula(AtomicFormula::Atom(Atom {
                        predicate_symbol: "p".into(),
                        terms: vec![]
                    }))
                    .into(),
                    rhs: Formula::AtomicFormula(AtomicFormula::Atom(Atom {
                        predicate_symbol: "q".into(),
                        terms: vec![]
                    }))
                    .into()
                }
                .into(),
                rhs: Formula::AtomicFormula(AtomicFormula::Atom(Atom {
                    predicate_symbol: "r".into(),
                    terms: vec![]
                }))
                .into(),
            })
            .to_string(),
            "p => q => r"
        );
        assert_eq!(
            Format(&Formula::QuantifiedFormula {
                quantification: Quantification {
                    quantifier: Quantifier::Forall,
                    variables: vec![
                        Variable {
                            name: "X".into(),
                            sort: Sort::Integer,
                        },
                        Variable {
                            name: "Y1".into(),
                            sort: Sort::General,
                        },
                    ]
                },
                formula: Formula::BinaryFormula {
                    connective: BinaryConnective::Conjunction,
                    lhs: Formula::AtomicFormula(AtomicFormula::Atom(Atom {
                        predicate_symbol: "p".into(),
                        terms: vec![],
                    }))
                    .into(),
                    rhs: Formula::AtomicFormula(AtomicFormula::Atom(Atom {
                        predicate_symbol: "q".into(),
                        terms: vec![],
                    }))
                    .into(),
                }
                .into()
            })
            .to_string(),
            "![X_i: $int, Y1_g: general]: (p & q)"
        );
        assert_eq!(
            Format(&Formula::QuantifiedFormula {
                quantification: Quantification {
                    quantifier: Quantifier::Forall,
                    variables: vec![
                        Variable {
                            name: "X_i".into(),
                            sort: Sort::Symbol,
                        },
                        Variable {
                            name: "X".into(),
                            sort: Sort::Integer,
                        },
                        Variable {
                            name: "Y1".into(),
                            sort: Sort::General,
                        },
                    ]
                },
                formula: Formula::BinaryFormula {
                    connective: BinaryConnective::Conjunction,
                    lhs: Formula::BinaryFormula {
                        connective: BinaryConnective::Conjunction,
                        lhs: Formula::AtomicFormula(AtomicFormula::Atom(Atom {
                            predicate_symbol: "p".into(),
                            terms: vec![GeneralTerm::IntegerTerm(IntegerTerm::Variable("X".to_string()))],
                        }))
                        .into(),
                        rhs: Formula::AtomicFormula(AtomicFormula::Atom(Atom {
                            predicate_symbol: "q".into(),
                            terms: vec![GeneralTerm::Variable("Y1".to_string())],
                        }))
                        .into(),
                    }.into(),
                    rhs: Formula::AtomicFormula(AtomicFormula::Atom(Atom {
                        predicate_symbol: "t".into(),
                        terms: vec![GeneralTerm::SymbolicTerm(SymbolicTerm::Variable("X_i".into()))],
                    }))
                    .into(),
                }.into()
            })
            .to_string(),
            "![X_i_s: symbol, X_i: $int, Y1_g: general]: (p(f__integer__(X_i)) & q(Y1_g) & t(f__symbolic__(X_i_s)))"
        );
    }
}
