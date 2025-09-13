use {
    crate::{
        formatting::{Associativity, Precedence},
        syntax_tree::{
            Node,
            fol::sigma_0::{
                AnnotatedFormula, Atom, AtomicFormula, BinaryConnective, BinaryOperator,
                Comparison, Direction, Formula, FunctionConstant, GeneralTerm, Guard, IntegerTerm,
                PlaceholderDeclaration, Predicate, Quantification, Quantifier, Relation, Role,
                Sort, Specification, SymbolicTerm, Theory, UnaryConnective, UnaryOperator,
                UserGuide, UserGuideEntry, Variable,
            },
        },
    },
    std::fmt::{self, Display, Formatter},
};

pub struct Format<'a, N: Node>(pub &'a N);

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
        }
    }
}

impl Format<'_, IntegerTerm> {}

impl Precedence for Format<'_, IntegerTerm> {
    fn precedence(&self) -> usize {
        match self.0 {
            IntegerTerm::Numeral(1..) => 1,
            IntegerTerm::UnaryOperation {
                op: UnaryOperator::Negative,
                ..
            }
            | IntegerTerm::Numeral(_)
            | IntegerTerm::FunctionConstant(_)
            | IntegerTerm::Variable(_) => 0,
            IntegerTerm::BinaryOperation {
                op: BinaryOperator::Multiply,
                ..
            } => 2,
            IntegerTerm::BinaryOperation {
                op: BinaryOperator::Add | BinaryOperator::Subtract,
                ..
            } => 3,
        }
    }

    fn associativity(&self) -> Associativity {
        Associativity::Left
    }

    fn fmt_operator(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self.0 {
            IntegerTerm::UnaryOperation { op, .. } => write!(f, "{}", Format(op)),
            IntegerTerm::BinaryOperation { op, .. } => write!(f, " {} ", Format(op)),
            IntegerTerm::Numeral(_)
            | IntegerTerm::Variable(_)
            | IntegerTerm::FunctionConstant(_) => unreachable!(),
        }
    }
}

impl Display for Format<'_, IntegerTerm> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self.0 {
            IntegerTerm::Numeral(n) => write!(f, "{n}"),
            IntegerTerm::FunctionConstant(c) => write!(f, "{c}$i"),
            IntegerTerm::Variable(v) => write!(f, "{v}$i"),
            IntegerTerm::UnaryOperation { arg, .. } => self.fmt_unary(Format(arg.as_ref()), f),
            IntegerTerm::BinaryOperation { lhs, rhs, .. } => {
                self.fmt_binary(Format(lhs.as_ref()), Format(rhs.as_ref()), f)
            }
        }
    }
}

impl Display for Format<'_, SymbolicTerm> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self.0 {
            SymbolicTerm::Symbol(s) => write!(f, "{s}"),
            SymbolicTerm::FunctionConstant(c) => write!(f, "{c}$s"),
            SymbolicTerm::Variable(v) => write!(f, "{v}$s"),
        }
    }
}

impl Display for Format<'_, GeneralTerm> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self.0 {
            GeneralTerm::Infimum => write!(f, "#inf"),
            GeneralTerm::Supremum => write!(f, "#sup"),
            GeneralTerm::FunctionConstant(c) => write!(f, "{c}$g"),
            GeneralTerm::Variable(v) => write!(f, "{v}"),
            GeneralTerm::IntegerTerm(t) => Format(t).fmt(f),
            GeneralTerm::SymbolicTerm(t) => Format(t).fmt(f),
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

impl Display for Format<'_, Relation> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self.0 {
            Relation::Equal => write!(f, "="),
            Relation::NotEqual => write!(f, "!="),
            Relation::GreaterEqual => write!(f, ">="),
            Relation::LessEqual => write!(f, "<="),
            Relation::Greater => write!(f, ">"),
            Relation::Less => write!(f, "<"),
        }
    }
}

impl Display for Format<'_, Guard> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{} {}", Format(&self.0.relation), Format(&self.0.term))
    }
}

impl Display for Format<'_, Comparison> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let guards = &self.0.guards;

        write!(f, "{}", Format(&self.0.term))?;

        let iter = guards.iter().map(Format);
        for guard in iter {
            write!(f, " {guard}")?;
        }

        Ok(())
    }
}

impl Display for Format<'_, AtomicFormula> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self.0 {
            AtomicFormula::Truth => write!(f, "#true"),
            AtomicFormula::Falsity => write!(f, "#false"),
            AtomicFormula::Atom(a) => Format(a).fmt(f),
            AtomicFormula::Comparison(c) => Format(c).fmt(f),
        }
    }
}

impl Display for Format<'_, Quantifier> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self.0 {
            Quantifier::Forall => write!(f, "forall"),
            Quantifier::Exists => write!(f, "exists"),
        }
    }
}

impl Display for Format<'_, FunctionConstant> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{}${}", self.0.name, Format(&self.0.sort))
    }
}

impl Display for Format<'_, Variable> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let name = &self.0.name;
        let sort = &self.0.sort;

        match sort {
            Sort::General => write!(f, "{name}"),
            Sort::Integer => write!(f, "{name}$i"),
            Sort::Symbol => write!(f, "{name}$s"),
        }
    }
}

impl Display for Format<'_, Sort> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self.0 {
            Sort::General => write!(f, "g"),
            Sort::Integer => write!(f, "i"),
            Sort::Symbol => write!(f, "s"),
        }
    }
}

impl Display for Format<'_, Quantification> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let quantifier = &self.0.quantifier;
        let variables = &self.0.variables;

        match quantifier {
            Quantifier::Forall => write!(f, "forall"),
            Quantifier::Exists => write!(f, "exists"),
        }?;

        let iter = variables.iter().map(Format);
        for var in iter {
            write!(f, " {var}")?;
        }

        Ok(())
    }
}

impl Display for Format<'_, UnaryConnective> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self.0 {
            UnaryConnective::Negation => write!(f, "not"),
        }
    }
}

impl Display for Format<'_, BinaryConnective> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self.0 {
            BinaryConnective::Equivalence => write!(f, "<->"),
            BinaryConnective::Implication => write!(f, "->"),
            BinaryConnective::ReverseImplication => write!(f, "<-"),
            BinaryConnective::Conjunction => write!(f, "and"),
            BinaryConnective::Disjunction => write!(f, "or"),
        }
    }
}

impl Precedence for Format<'_, Formula> {
    fn precedence(&self) -> usize {
        match self.0 {
            Formula::AtomicFormula(_) => 0,
            Formula::UnaryFormula { .. } | Formula::QuantifiedFormula { .. } => 1,
            Formula::BinaryFormula {
                connective: BinaryConnective::Conjunction,
                ..
            } => 2,
            Formula::BinaryFormula {
                connective: BinaryConnective::Disjunction,
                ..
            } => 3,
            Formula::BinaryFormula {
                connective:
                    BinaryConnective::Equivalence
                    | BinaryConnective::Implication
                    | BinaryConnective::ReverseImplication,
                ..
            } => 4,
        }
    }

    fn associativity(&self) -> Associativity {
        match self.0 {
            Formula::UnaryFormula { .. }
            | Formula::QuantifiedFormula { .. }
            | Formula::BinaryFormula {
                connective:
                    BinaryConnective::Conjunction
                    | BinaryConnective::Disjunction
                    | BinaryConnective::ReverseImplication,
                ..
            } => Associativity::Left,
            Formula::BinaryFormula {
                connective: BinaryConnective::Equivalence | BinaryConnective::Implication,
                ..
            } => Associativity::Right,
            Formula::AtomicFormula(_) => unreachable!(),
        }
    }

    fn mandatory_parentheses(&self) -> bool {
        matches!(
            self.0,
            Formula::BinaryFormula {
                connective: BinaryConnective::Equivalence
                    | BinaryConnective::Implication
                    | BinaryConnective::ReverseImplication,
                ..
            }
        )
    }

    fn fmt_operator(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self.0 {
            Formula::UnaryFormula { connective, .. } => write!(f, "{} ", Format(connective)),
            Formula::QuantifiedFormula { quantification, .. } => {
                write!(f, "{} ", Format(quantification))
            }
            Formula::BinaryFormula { connective, .. } => write!(f, " {} ", Format(connective)),
            Formula::AtomicFormula(_) => unreachable!(),
        }
    }
}

impl Display for Format<'_, Formula> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self.0 {
            Formula::AtomicFormula(a) => Format(a).fmt(f),
            Formula::UnaryFormula { formula, .. } => self.fmt_unary(Format(formula.as_ref()), f),
            Formula::QuantifiedFormula { formula, .. } => {
                self.fmt_unary(Format(formula.as_ref()), f)
            }
            Formula::BinaryFormula { lhs, rhs, .. } => {
                self.fmt_binary(Format(lhs.as_ref()), Format(rhs.as_ref()), f)
            }
        }
    }
}

impl Display for Format<'_, Theory> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let formulas = &self.0.formulas;
        let iter = formulas.iter().map(Format);
        for form in iter {
            writeln!(f, "{form}.")?;
        }
        Ok(())
    }
}

impl Display for Format<'_, Role> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self.0 {
            Role::Assumption => write!(f, "assumption"),
            Role::Spec => write!(f, "spec"),
            Role::Lemma => write!(f, "lemma"),
            Role::Definition => write!(f, "definition"),
            Role::InductiveLemma => write!(f, "inductive-lemma"),
        }
    }
}

impl Display for Format<'_, Direction> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self.0 {
            Direction::Universal => write!(f, "universal"),
            Direction::Forward => write!(f, "forward"),
            Direction::Backward => write!(f, "backward"),
        }
    }
}

impl Display for Format<'_, AnnotatedFormula> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        Format(&self.0.role).fmt(f)?;

        if !matches!(self.0.direction, Direction::Universal) {
            write!(f, "({})", Format(&self.0.direction))?
        }

        if !self.0.name.is_empty() {
            write!(f, "[{}]", self.0.name)?;
        }

        write!(f, ": ")?;

        Format(&self.0.formula).fmt(f)?;

        Ok(())
    }
}

impl Display for Format<'_, Specification> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let iter = self.0.formulas.iter().map(Format);
        for formula in iter {
            writeln!(f, "{formula}.")?;
        }
        Ok(())
    }
}

impl Display for Format<'_, PlaceholderDeclaration> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{} -> {}", &self.0.name, Format(&self.0.sort))
    }
}

impl Display for Format<'_, UserGuideEntry> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self.0 {
            UserGuideEntry::InputPredicate(p) => write!(f, "input: {}", Format(p)),
            UserGuideEntry::OutputPredicate(p) => write!(f, "output: {}", Format(p)),
            UserGuideEntry::PlaceholderDeclaration(c) => write!(f, "input: {}", Format(c)),
            UserGuideEntry::AnnotatedFormula(g) => Format(g).fmt(f),
        }
    }
}

impl Display for Format<'_, UserGuide> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let iter = self.0.entries.iter().map(Format);
        for entry in iter {
            writeln!(f, "{entry}.")?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use {
        super::Format,
        crate::syntax_tree::fol::sigma_0::{
            AnnotatedFormula, Atom, AtomicFormula, BinaryConnective, BinaryOperator, Comparison,
            Direction, Formula, GeneralTerm, Guard, IntegerTerm, PlaceholderDeclaration, Predicate,
            Quantification, Quantifier, Relation, Role, Sort, Specification, SymbolicTerm, Theory,
            UnaryConnective, UnaryOperator, UserGuide, UserGuideEntry, Variable,
        },
    };

    #[test]
    fn format_unary_operator() {
        assert_eq!(Format(&UnaryOperator::Negative).to_string(), "-");
    }

    #[test]
    fn format_binary_operator() {
        for (left, right) in [
            (BinaryOperator::Add, "+"),
            (BinaryOperator::Subtract, "-"),
            (BinaryOperator::Multiply, "*"),
        ] {
            assert_eq!(Format(&left).to_string(), right);
        }
    }

    #[test]
    fn format_relation() {
        for (left, right) in [
            (Relation::Less, "<"),
            (Relation::Greater, ">"),
            (Relation::LessEqual, "<="),
            (Relation::GreaterEqual, ">="),
            (Relation::Equal, "="),
            (Relation::NotEqual, "!="),
        ] {
            assert_eq!(Format(&left).to_string(), right);
        }
    }

    #[test]
    fn format_unary_connective() {
        assert_eq!(Format(&UnaryConnective::Negation).to_string(), "not");
    }

    #[test]
    fn format_binary_connective() {
        for (left, right) in [
            (BinaryConnective::Conjunction, "and"),
            (BinaryConnective::Disjunction, "or"),
            (BinaryConnective::Implication, "->"),
            (BinaryConnective::ReverseImplication, "<-"),
            (BinaryConnective::Equivalence, "<->"),
        ] {
            assert_eq!(Format(&left).to_string(), right);
        }
    }

    #[test]
    fn format_quantifier() {
        for (left, right) in [
            (Quantifier::Forall, "forall"),
            (Quantifier::Exists, "exists"),
        ] {
            assert_eq!(Format(&left).to_string(), right);
        }
    }

    #[test]
    fn format_sort() {
        for (left, right) in [
            (Sort::General, "g"),
            (Sort::Integer, "i"),
            (Sort::Symbol, "s"),
        ] {
            assert_eq!(Format(&left).to_string(), right);
        }
    }

    #[test]
    fn format_integer_term() {
        assert_eq!(Format(&IntegerTerm::Numeral(-1)).to_string(), "-1");
        assert_eq!(Format(&IntegerTerm::Numeral(0)).to_string(), "0");
        assert_eq!(Format(&IntegerTerm::Numeral(42)).to_string(), "42");
        assert_eq!(
            Format(&IntegerTerm::Variable("A".into())).to_string(),
            "A$i"
        );
    }

    #[test]
    fn format_general_term() {
        assert_eq!(Format(&GeneralTerm::Infimum).to_string(), "#inf");
        assert_eq!(Format(&GeneralTerm::Supremum).to_string(), "#sup");
        assert_eq!(
            Format(&GeneralTerm::IntegerTerm(IntegerTerm::Variable("N".into()))).to_string(),
            "N$i"
        );
        assert_eq!(
            Format(&GeneralTerm::SymbolicTerm(SymbolicTerm::Symbol(
                "abc".into()
            )))
            .to_string(),
            "abc"
        );
        assert_eq!(
            Format(&GeneralTerm::IntegerTerm(IntegerTerm::BinaryOperation {
                op: BinaryOperator::Multiply,
                lhs: IntegerTerm::Numeral(1).into(),
                rhs: IntegerTerm::Numeral(5).into(),
            }))
            .to_string(),
            "1 * 5"
        );
    }

    #[test]
    fn format_comparison() {
        assert_eq!(
            Format(&Comparison {
                term: GeneralTerm::IntegerTerm(IntegerTerm::Numeral(1)),
                guards: vec![Guard {
                    relation: Relation::Less,
                    term: GeneralTerm::IntegerTerm(IntegerTerm::Numeral(5)),
                }]
            })
            .to_string(),
            "1 < 5"
        );
        assert_eq!(
            Format(&Comparison {
                term: GeneralTerm::IntegerTerm(IntegerTerm::Variable("N".into())),
                guards: vec![
                    Guard {
                        relation: Relation::Less,
                        term: GeneralTerm::IntegerTerm(IntegerTerm::Numeral(5)),
                    },
                    Guard {
                        relation: Relation::NotEqual,
                        term: GeneralTerm::IntegerTerm(IntegerTerm::BinaryOperation {
                            op: BinaryOperator::Multiply,
                            lhs: IntegerTerm::Numeral(7).into(),
                            rhs: IntegerTerm::Numeral(2).into(),
                        }),
                    },
                    Guard {
                        relation: Relation::GreaterEqual,
                        term: GeneralTerm::IntegerTerm(IntegerTerm::Variable("Xa".into())),
                    },
                ]
            })
            .to_string(),
            "N$i < 5 != 7 * 2 >= Xa$i"
        );
    }

    #[test]
    fn format_quantification() {
        assert_eq!(
            Format(&Quantification {
                quantifier: Quantifier::Forall,
                variables: vec![
                    Variable {
                        name: "X".into(),
                        sort: Sort::General,
                    },
                    Variable {
                        name: "Y".into(),
                        sort: Sort::Integer,
                    },
                    Variable {
                        name: "N".into(),
                        sort: Sort::General,
                    },
                ]
            })
            .to_string(),
            "forall X Y$i N"
        );
    }

    #[test]
    fn format_atomic_formula() {
        assert_eq!(
            Format(&AtomicFormula::Atom(Atom {
                predicate_symbol: "p".into(),
                terms: vec![
                    GeneralTerm::SymbolicTerm(SymbolicTerm::Symbol("a".into())),
                    GeneralTerm::IntegerTerm(IntegerTerm::Variable("X".into())),
                ]
            }))
            .to_string(),
            "p(a, X$i)"
        );
        assert_eq!(
            Format(&AtomicFormula::Comparison(Comparison {
                term: GeneralTerm::IntegerTerm(IntegerTerm::Numeral(5)),
                guards: vec![Guard {
                    relation: Relation::Less,
                    term: GeneralTerm::Variable("I".into()),
                }]
            }))
            .to_string(),
            "5 < I"
        );
        assert_eq!(Format(&AtomicFormula::Falsity).to_string(), "#false");
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
            Format(&Formula::UnaryFormula {
                connective: UnaryConnective::Negation,
                formula: Formula::AtomicFormula(AtomicFormula::Atom(Atom {
                    predicate_symbol: "p".into(),
                    terms: vec![]
                }))
                .into()
            })
            .to_string(),
            "not p"
        );

        assert_eq!(
            Format(&Formula::QuantifiedFormula {
                quantification: Quantification {
                    quantifier: Quantifier::Forall,
                    variables: vec![Variable {
                        name: "X".into(),
                        sort: Sort::General
                    }]
                },
                formula: Formula::AtomicFormula(AtomicFormula::Atom(Atom {
                    predicate_symbol: "p".into(),
                    terms: vec![GeneralTerm::Variable("X".into())]
                }))
                .into()
            })
            .to_string(),
            "forall X p(X)"
        );

        assert_eq!(
            Format(&Formula::BinaryFormula {
                connective: BinaryConnective::ReverseImplication,
                lhs: Formula::BinaryFormula {
                    connective: BinaryConnective::ReverseImplication,
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
            "(p <- q) <- r"
        );

        assert_eq!(
            Format(&Formula::BinaryFormula {
                connective: BinaryConnective::ReverseImplication,
                lhs: Formula::AtomicFormula(AtomicFormula::Atom(Atom {
                    predicate_symbol: "p".into(),
                    terms: vec![]
                }))
                .into(),
                rhs: Formula::BinaryFormula {
                    connective: BinaryConnective::ReverseImplication,
                    lhs: Formula::AtomicFormula(AtomicFormula::Atom(Atom {
                        predicate_symbol: "q".into(),
                        terms: vec![]
                    }))
                    .into(),
                    rhs: Formula::AtomicFormula(AtomicFormula::Atom(Atom {
                        predicate_symbol: "r".into(),
                        terms: vec![]
                    }))
                    .into()
                }
                .into()
            })
            .to_string(),
            "p <- (q <- r)"
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
            "(p -> q) -> r"
        );

        assert_eq!(
            Format(&Formula::BinaryFormula {
                connective: BinaryConnective::Implication,
                lhs: Formula::AtomicFormula(AtomicFormula::Atom(Atom {
                    predicate_symbol: "p".into(),
                    terms: vec![]
                }))
                .into(),
                rhs: Formula::BinaryFormula {
                    connective: BinaryConnective::Implication,
                    lhs: Formula::AtomicFormula(AtomicFormula::Atom(Atom {
                        predicate_symbol: "q".into(),
                        terms: vec![]
                    }))
                    .into(),
                    rhs: Formula::AtomicFormula(AtomicFormula::Atom(Atom {
                        predicate_symbol: "r".into(),
                        terms: vec![]
                    }))
                    .into()
                }
                .into()
            })
            .to_string(),
            "p -> (q -> r)"
        );

        assert_eq!(
            Format(&Formula::BinaryFormula {
                connective: BinaryConnective::ReverseImplication,
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
            "(p -> q) <- r"
        );

        assert_eq!(
            Format(&Formula::BinaryFormula {
                connective: BinaryConnective::Implication,
                lhs: Formula::AtomicFormula(AtomicFormula::Atom(Atom {
                    predicate_symbol: "p".into(),
                    terms: vec![]
                }))
                .into(),
                rhs: Formula::BinaryFormula {
                    connective: BinaryConnective::ReverseImplication,
                    lhs: Formula::AtomicFormula(AtomicFormula::Atom(Atom {
                        predicate_symbol: "q".into(),
                        terms: vec![]
                    }))
                    .into(),
                    rhs: Formula::AtomicFormula(AtomicFormula::Atom(Atom {
                        predicate_symbol: "r".into(),
                        terms: vec![]
                    }))
                    .into()
                }
                .into()
            })
            .to_string(),
            "p -> (q <- r)"
        );

        assert_eq!(
            Format(&Formula::BinaryFormula {
                connective: BinaryConnective::Implication,
                lhs: Formula::BinaryFormula {
                    connective: BinaryConnective::ReverseImplication,
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
            "(p <- q) -> r"
        );

        assert_eq!(
            Format(&Formula::BinaryFormula {
                connective: BinaryConnective::ReverseImplication,
                lhs: Formula::AtomicFormula(AtomicFormula::Atom(Atom {
                    predicate_symbol: "p".into(),
                    terms: vec![]
                }))
                .into(),
                rhs: Formula::BinaryFormula {
                    connective: BinaryConnective::Implication,
                    lhs: Formula::AtomicFormula(AtomicFormula::Atom(Atom {
                        predicate_symbol: "q".into(),
                        terms: vec![]
                    }))
                    .into(),
                    rhs: Formula::AtomicFormula(AtomicFormula::Atom(Atom {
                        predicate_symbol: "r".into(),
                        terms: vec![]
                    }))
                    .into()
                }
                .into()
            })
            .to_string(),
            "p <- (q -> r)"
        );
    }

    #[test]
    fn format_theory() {
        assert_eq!(
            Format(&Theory {
                formulas: vec![
                    Formula::AtomicFormula(AtomicFormula::Truth).into(),
                    Formula::BinaryFormula {
                        connective: BinaryConnective::Equivalence,
                        lhs: Formula::AtomicFormula(AtomicFormula::Atom(Atom {
                            predicate_symbol: "p".to_string(),
                            terms: vec![]
                        }))
                        .into(),
                        rhs: Formula::AtomicFormula(AtomicFormula::Atom(Atom {
                            predicate_symbol: "q".to_string(),
                            terms: vec![]
                        }))
                        .into()
                    }
                ],
            })
            .to_string(),
            "#true.\np <-> q.\n"
        );
    }

    #[test]
    fn format_role() {
        for (left, right) in [
            (Role::Assumption, "assumption"),
            (Role::Spec, "spec"),
            (Role::Lemma, "lemma"),
            (Role::Definition, "definition"),
            (Role::InductiveLemma, "inductive-lemma"),
        ] {
            assert_eq!(Format(&left).to_string(), right);
        }
    }

    #[test]
    fn format_direction() {
        for (left, right) in [
            (Direction::Universal, "universal"),
            (Direction::Forward, "forward"),
            (Direction::Backward, "backward"),
        ] {
            assert_eq!(Format(&left).to_string(), right);
        }
    }

    #[test]
    fn format_annotated_formula() {
        for (left, right) in [
            (
                AnnotatedFormula {
                    role: Role::Lemma,
                    direction: Direction::Universal,
                    name: "lemma_p".to_string(),
                    formula: Formula::AtomicFormula(AtomicFormula::Atom(Atom {
                        predicate_symbol: "p".to_string(),
                        terms: vec![GeneralTerm::IntegerTerm(IntegerTerm::Numeral(1))],
                    })),
                },
                "lemma[lemma_p]: p(1)",
            ),
            (
                AnnotatedFormula {
                    role: Role::Assumption,
                    direction: Direction::Forward,
                    name: String::default(),
                    formula: Formula::BinaryFormula {
                        connective: BinaryConnective::Disjunction,
                        lhs: Formula::AtomicFormula(AtomicFormula::Truth).into(),
                        rhs: Formula::AtomicFormula(AtomicFormula::Falsity).into(),
                    },
                },
                "assumption(forward): #true or #false",
            ),
        ] {
            assert_eq!(Format(&left).to_string(), right);
        }
    }

    #[test]
    fn format_specification() {
        let left = Format(&Specification {
            formulas: vec![
                AnnotatedFormula {
                    role: Role::Spec,
                    direction: Direction::Forward,
                    name: "about_p_0".to_string(),
                    formula: Formula::UnaryFormula {
                        connective: UnaryConnective::Negation,
                        formula: Formula::AtomicFormula(AtomicFormula::Atom(Atom {
                            predicate_symbol: "p".into(),
                            terms: vec![GeneralTerm::IntegerTerm(IntegerTerm::Numeral(0))],
                        }))
                        .into(),
                    },
                },
                AnnotatedFormula {
                    role: Role::Assumption,
                    direction: Direction::Universal,
                    name: String::default(),
                    formula: Formula::AtomicFormula(AtomicFormula::Atom(Atom {
                        predicate_symbol: "p".into(),
                        terms: vec![GeneralTerm::IntegerTerm(IntegerTerm::Numeral(5))],
                    })),
                },
                AnnotatedFormula {
                    role: Role::InductiveLemma,
                    direction: Direction::Backward,
                    name: "il1".to_string(),
                    formula: Formula::QuantifiedFormula {
                        quantification: Quantification {
                            quantifier: Quantifier::Forall,
                            variables: vec![Variable {
                                name: "X".into(),
                                sort: Sort::General,
                            }],
                        },
                        formula: Formula::BinaryFormula {
                            connective: BinaryConnective::Equivalence,
                            lhs: Formula::AtomicFormula(AtomicFormula::Atom(Atom {
                                predicate_symbol: "p".into(),
                                terms: vec![GeneralTerm::Variable("X".into())],
                            }))
                            .into(),
                            rhs: Formula::BinaryFormula {
                                connective: BinaryConnective::Disjunction,
                                lhs: Formula::AtomicFormula(AtomicFormula::Atom(Atom {
                                    predicate_symbol: "q".into(),
                                    terms: vec![GeneralTerm::Variable("X".into())],
                                }))
                                .into(),
                                rhs: Formula::AtomicFormula(AtomicFormula::Atom(Atom {
                                    predicate_symbol: "t".into(),
                                    terms: vec![],
                                }))
                                .into(),
                            }
                            .into(),
                        }
                        .into(),
                    },
                },
            ],
        })
        .to_string();
        let right = "spec(forward)[about_p_0]: not p(0).\nassumption: p(5).\ninductive-lemma(backward)[il1]: forall X (p(X) <-> q(X) or t).\n".to_string();
        assert_eq!(left, right, "\n{left}!=\n{right}");
    }

    #[test]
    fn format_placeholder_declaration() {
        assert_eq!(
            Format(&PlaceholderDeclaration {
                name: "n".to_string(),
                sort: Sort::Integer,
            })
            .to_string(),
            "n -> i"
        );
    }

    #[test]
    fn format_user_guide_entry() {
        for (left, right) in [
            (
                UserGuideEntry::InputPredicate(Predicate {
                    symbol: "p".to_string(),
                    arity: 0,
                }),
                "input: p/0",
            ),
            (
                UserGuideEntry::OutputPredicate(Predicate {
                    symbol: "q".to_string(),
                    arity: 1,
                }),
                "output: q/1",
            ),
            (
                UserGuideEntry::PlaceholderDeclaration(PlaceholderDeclaration {
                    name: "a".to_string(),
                    sort: Sort::Symbol,
                }),
                "input: a -> s",
            ),
            (
                UserGuideEntry::AnnotatedFormula(AnnotatedFormula {
                    role: Role::Lemma,
                    direction: Direction::Backward,
                    name: String::default(),
                    formula: Formula::UnaryFormula {
                        connective: UnaryConnective::Negation,
                        formula: Formula::AtomicFormula(AtomicFormula::Atom(Atom {
                            predicate_symbol: "p".to_string(),
                            terms: vec![GeneralTerm::IntegerTerm(IntegerTerm::Numeral(1))],
                        }))
                        .into(),
                    },
                }),
                "lemma(backward): not p(1)",
            ),
        ] {
            assert_eq!(Format(&left).to_string(), right);
        }
    }

    #[test]
    fn format_user_guide() {
        assert_eq!(
            Format(&UserGuide {
                entries: vec![
                    UserGuideEntry::PlaceholderDeclaration(PlaceholderDeclaration {
                        name: "n".to_string(),
                        sort: Sort::Integer,
                    }),
                    UserGuideEntry::OutputPredicate(Predicate {
                        symbol: "q".to_string(),
                        arity: 2,
                    }),
                ],
            })
            .to_string(),
            "input: n -> i.\noutput: q/2.\n",
        );
    }
}
