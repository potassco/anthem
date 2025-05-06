use crate::{
    parsing::PestParser,
    syntax_tree::asp::{
        Aggregate, AggregateAtom, AggregateOperation, AggregateOrder, Atom, AtomicFormula,
        BinaryOperator, Body, Comparison, Head, Literal, PrecomputedTerm, Predicate, Program,
        Relation, Rule, Sign, Term, UnaryOperator, Variable,
    },
};

mod internal {
    use pest::pratt_parser::PrattParser;

    #[derive(pest_derive::Parser)]
    #[grammar = "parsing/asp/grammar.pest"]
    pub struct Parser;

    lazy_static::lazy_static! {
        pub static ref PRATT_PARSER: PrattParser<Rule> = {
            use pest::pratt_parser::{Assoc::*, Op};
            use Rule::*;

            PrattParser::new()
                .op(Op::infix(interval, Left))
                .op(Op::infix(add, Left) | Op::infix(subtract, Left))
                .op(Op::infix(multiply, Left) | Op::infix(divide, Left) | Op::infix(modulo, Left))
                .op(Op::prefix(negative))
        };
    }
}

pub struct PrecomputedTermParser;

impl PestParser for PrecomputedTermParser {
    type Node = PrecomputedTerm;

    type InternalParser = internal::Parser;
    type Rule = internal::Rule;
    const RULE: internal::Rule = internal::Rule::precomputed_term_eoi;

    fn translate_pair(pair: pest::iterators::Pair<'_, Self::Rule>) -> Self::Node {
        match pair.as_rule() {
            internal::Rule::precomputed_term => Self::translate_pairs(pair.into_inner()),
            internal::Rule::infimum => PrecomputedTerm::Infimum,
            internal::Rule::integer => PrecomputedTerm::Numeral(pair.as_str().parse().unwrap()),
            internal::Rule::symbol => PrecomputedTerm::Symbol(pair.as_str().into()),
            internal::Rule::supremum => PrecomputedTerm::Supremum,
            _ => Self::report_unexpected_pair(pair),
        }
    }
}

pub struct VariableParser;

impl PestParser for VariableParser {
    type Node = Variable;

    type InternalParser = internal::Parser;
    type Rule = internal::Rule;
    const RULE: internal::Rule = internal::Rule::variable_eoi;

    fn translate_pair(pair: pest::iterators::Pair<'_, Self::Rule>) -> Self::Node {
        if pair.as_rule() != internal::Rule::variable {
            Self::report_unexpected_pair(pair)
        }

        Variable(pair.as_str().into())
    }
}

pub struct UnaryOperatorParser;

impl PestParser for UnaryOperatorParser {
    type Node = UnaryOperator;

    type InternalParser = internal::Parser;
    type Rule = internal::Rule;
    const RULE: internal::Rule = internal::Rule::unary_operator_eoi;

    fn translate_pair(pair: pest::iterators::Pair<'_, Self::Rule>) -> Self::Node {
        match pair.as_rule() {
            internal::Rule::negative => UnaryOperator::Negative,
            _ => Self::report_unexpected_pair(pair),
        }
    }
}

pub struct BinaryOperatorParser;

impl PestParser for BinaryOperatorParser {
    type Node = BinaryOperator;

    type InternalParser = internal::Parser;
    type Rule = internal::Rule;
    const RULE: internal::Rule = internal::Rule::binary_operator_eoi;

    fn translate_pair(pair: pest::iterators::Pair<'_, Self::Rule>) -> Self::Node {
        match pair.as_rule() {
            internal::Rule::add => BinaryOperator::Add,
            internal::Rule::subtract => BinaryOperator::Subtract,
            internal::Rule::multiply => BinaryOperator::Multiply,
            internal::Rule::divide => BinaryOperator::Divide,
            internal::Rule::modulo => BinaryOperator::Modulo,
            internal::Rule::interval => BinaryOperator::Interval,
            _ => Self::report_unexpected_pair(pair),
        }
    }
}

pub struct TermParser;

impl PestParser for TermParser {
    type Node = Term;

    type InternalParser = internal::Parser;
    type Rule = internal::Rule;
    const RULE: internal::Rule = internal::Rule::term_eoi;

    fn translate_pair(pair: pest::iterators::Pair<'_, Self::Rule>) -> Self::Node {
        internal::PRATT_PARSER
            .map_primary(|primary| match primary.as_rule() {
                internal::Rule::term => TermParser::translate_pair(primary),
                internal::Rule::precomputed_term => {
                    Term::PrecomputedTerm(PrecomputedTermParser::translate_pair(primary))
                }
                internal::Rule::variable => Term::Variable(VariableParser::translate_pair(primary)),
                _ => Self::report_unexpected_pair(primary),
            })
            .map_prefix(|op, arg| Term::UnaryOperation {
                op: UnaryOperatorParser::translate_pair(op),
                arg: Box::new(arg),
            })
            .map_infix(|lhs, op, rhs| Term::BinaryOperation {
                op: BinaryOperatorParser::translate_pair(op),
                lhs: Box::new(lhs),
                rhs: Box::new(rhs),
            })
            .parse(pair.into_inner())
    }
}

pub struct PredicateParser;

impl PestParser for PredicateParser {
    type Node = Predicate;

    type InternalParser = internal::Parser;
    type Rule = internal::Rule;
    const RULE: Self::Rule = internal::Rule::predicate_eoi;

    fn translate_pair(pair: pest::iterators::Pair<'_, Self::Rule>) -> Self::Node {
        if pair.as_rule() != internal::Rule::predicate {
            Self::report_unexpected_pair(pair)
        }

        let mut pairs = pair.into_inner();
        let symbol = pairs
            .next()
            .unwrap_or_else(|| Self::report_missing_pair())
            .as_str()
            .into();
        let arity_string: &str = pairs
            .next()
            .unwrap_or_else(|| Self::report_missing_pair())
            .as_str();
        let arity: usize = arity_string.parse().unwrap();

        Predicate { symbol, arity }
    }
}

pub struct AtomParser;

impl PestParser for AtomParser {
    type Node = Atom;

    type InternalParser = internal::Parser;
    type Rule = internal::Rule;
    const RULE: Self::Rule = internal::Rule::atom_eoi;

    fn translate_pair(pair: pest::iterators::Pair<'_, Self::Rule>) -> Self::Node {
        if pair.as_rule() != internal::Rule::atom {
            Self::report_unexpected_pair(pair)
        }

        let mut pairs = pair.into_inner();

        let predicate = pairs
            .next()
            .unwrap_or_else(|| Self::report_missing_pair())
            .as_str()
            .into();
        let terms: Vec<_> = pairs.map(TermParser::translate_pair).collect();

        Atom {
            predicate_symbol: predicate,
            terms,
        }
    }
}

pub struct SignParser;

impl PestParser for SignParser {
    type Node = Sign;

    type InternalParser = internal::Parser;
    type Rule = internal::Rule;
    const RULE: Self::Rule = internal::Rule::sign_eoi;

    fn translate_pair(pair: pest::iterators::Pair<'_, Self::Rule>) -> Self::Node {
        if pair.as_rule() != internal::Rule::sign {
            Self::report_unexpected_pair(pair)
        }

        let mut pairs = pair.into_inner();
        let mut result = Sign::NoSign;

        match pairs.next() {
            None => return result,
            Some(pair) if pair.as_rule() == internal::Rule::negation => {
                result = Sign::Negation;
            }
            Some(pair) => Self::report_unexpected_pair(pair),
        }

        match pairs.next() {
            None => return result,
            Some(pair) if pair.as_rule() == internal::Rule::negation => {
                result = Sign::DoubleNegation;
            }
            Some(pair) => Self::report_unexpected_pair(pair),
        }

        match pairs.next() {
            None => result,
            Some(pair) => Self::report_unexpected_pair(pair),
        }
    }
}

pub struct LiteralParser;

impl PestParser for LiteralParser {
    type Node = Literal;

    type InternalParser = internal::Parser;
    type Rule = internal::Rule;
    const RULE: Self::Rule = internal::Rule::literal_eoi;

    fn translate_pair(pair: pest::iterators::Pair<'_, Self::Rule>) -> Self::Node {
        if pair.as_rule() != internal::Rule::literal {
            Self::report_unexpected_pair(pair)
        }

        let mut pairs = pair.into_inner();

        let sign =
            SignParser::translate_pair(pairs.next().unwrap_or_else(|| Self::report_missing_pair()));
        let atom =
            AtomParser::translate_pair(pairs.next().unwrap_or_else(|| Self::report_missing_pair()));

        if let Some(pair) = pairs.next() {
            Self::report_unexpected_pair(pair)
        }

        Literal { sign, atom }
    }
}

pub struct RelationParser;

impl PestParser for RelationParser {
    type Node = Relation;

    type InternalParser = internal::Parser;
    type Rule = internal::Rule;
    const RULE: internal::Rule = internal::Rule::relation_eoi;

    fn translate_pair(pair: pest::iterators::Pair<'_, Self::Rule>) -> Self::Node {
        match pair.as_rule() {
            internal::Rule::equal => Relation::Equal,
            internal::Rule::not_equal => Relation::NotEqual,
            internal::Rule::less => Relation::Less,
            internal::Rule::less_equal => Relation::LessEqual,
            internal::Rule::greater => Relation::Greater,
            internal::Rule::greater_equal => Relation::GreaterEqual,
            _ => Self::report_unexpected_pair(pair),
        }
    }
}

pub struct ComparisonParser;

impl PestParser for ComparisonParser {
    type Node = Comparison;

    type InternalParser = internal::Parser;
    type Rule = internal::Rule;
    const RULE: Self::Rule = internal::Rule::comparison_eoi;

    fn translate_pair(pair: pest::iterators::Pair<'_, Self::Rule>) -> Self::Node {
        if pair.as_rule() != internal::Rule::comparison {
            Self::report_unexpected_pair(pair)
        }

        let mut pairs = pair.into_inner();

        let lhs =
            TermParser::translate_pair(pairs.next().unwrap_or_else(|| Self::report_missing_pair()));
        let relation = RelationParser::translate_pair(
            pairs.next().unwrap_or_else(|| Self::report_missing_pair()),
        );
        let rhs =
            TermParser::translate_pair(pairs.next().unwrap_or_else(|| Self::report_missing_pair()));

        if let Some(pair) = pairs.next() {
            Self::report_unexpected_pair(pair)
        }

        Comparison { relation, lhs, rhs }
    }
}

pub struct AtomicFormulaParser;

impl PestParser for AtomicFormulaParser {
    type Node = AtomicFormula;

    type InternalParser = internal::Parser;
    type Rule = internal::Rule;
    const RULE: internal::Rule = internal::Rule::atomic_formula_eoi;

    fn translate_pair(pair: pest::iterators::Pair<'_, Self::Rule>) -> Self::Node {
        match pair.as_rule() {
            internal::Rule::atomic_formula => {
                AtomicFormulaParser::translate_pairs(pair.into_inner())
            }
            internal::Rule::literal => AtomicFormula::Literal(LiteralParser::translate_pair(pair)),
            internal::Rule::comparison => {
                AtomicFormula::Comparison(ComparisonParser::translate_pair(pair))
            }
            _ => Self::report_unexpected_pair(pair),
        }
    }
}

pub struct AggregateParser;

impl PestParser for AggregateParser {
    type Node = Aggregate;

    type InternalParser = internal::Parser;
    type Rule = internal::Rule;
    const RULE: internal::Rule = internal::Rule::aggregate_eoi;

    fn translate_pair(pair: pest::iterators::Pair<'_, Self::Rule>) -> Self::Node {
        if pair.as_rule() != internal::Rule::aggregate {
            Self::report_unexpected_pair(pair)
        }

        let mut pairs = pair.into_inner().peekable();

        let mut variable_list = Vec::new();
        let mut conditions = Vec::new();

        let leading_variable = pairs
            .next()
            .map(VariableParser::translate_pair)
            .unwrap_or_else(|| Self::report_missing_pair());

        variable_list.push(leading_variable);

        while pairs.peek().is_some() {
            let pair = pairs.next().unwrap();
            match pair.as_rule() {
                internal::Rule::variable => {
                    //variable_list.push(VariableParser::translate_pairs(pair.into_inner()));
                    variable_list.push(VariableParser::translate_pair(pair));
                }
                internal::Rule::atomic_formula => {
                    //conditions.push(AtomicFormulaParser::translate_pairs(pair.into_inner()));
                    conditions.push(AtomicFormulaParser::translate_pair(pair));
                }
                _ => Self::report_unexpected_pair(pair),
            }
        }

        Aggregate {
            operation: AggregateOperation::Count,
            variable_list,
            conditions,
        }
    }
}

pub struct AggregateAtomParser;

impl PestParser for AggregateAtomParser {
    type Node = AggregateAtom;

    type InternalParser = internal::Parser;
    type Rule = internal::Rule;
    const RULE: internal::Rule = internal::Rule::aggregate_atom_eoi;

    fn translate_pair(pair: pest::iterators::Pair<'_, Self::Rule>) -> Self::Node {
        match pair.as_rule() {
            internal::Rule::aggregate_atom => {
                AggregateAtomParser::translate_pairs(pair.into_inner())
            }
            internal::Rule::left_aggregate => {
                let mut pairs = pair.into_inner();

                let aggregate = AggregateParser::translate_pair(
                    pairs.next().unwrap_or_else(|| Self::report_missing_pair()),
                );

                let relation = RelationParser::translate_pair(
                    pairs.next().unwrap_or_else(|| Self::report_missing_pair()),
                );

                let guard = TermParser::translate_pair(
                    pairs.next().unwrap_or_else(|| Self::report_missing_pair()),
                );

                AggregateAtom {
                    aggregate,
                    relation,
                    guard,
                    order: AggregateOrder::Left,
                }
            }
            internal::Rule::right_aggregate => {
                let mut pairs = pair.into_inner();

                let guard = TermParser::translate_pair(
                    pairs.next().unwrap_or_else(|| Self::report_missing_pair()),
                );

                let relation = RelationParser::translate_pair(
                    pairs.next().unwrap_or_else(|| Self::report_missing_pair()),
                );

                let aggregate = AggregateParser::translate_pair(
                    pairs.next().unwrap_or_else(|| Self::report_missing_pair()),
                );

                AggregateAtom {
                    aggregate,
                    relation,
                    guard,
                    order: AggregateOrder::Right,
                }
            }
            _ => Self::report_unexpected_pair(pair),
        }
    }
}

pub struct HeadParser;

impl PestParser for HeadParser {
    type Node = Head;

    type InternalParser = internal::Parser;
    type Rule = internal::Rule;
    const RULE: internal::Rule = internal::Rule::head_eoi;

    fn translate_pair(pair: pest::iterators::Pair<'_, Self::Rule>) -> Self::Node {
        match pair.as_rule() {
            internal::Rule::head => HeadParser::translate_pairs(pair.into_inner()),
            internal::Rule::basic_head => {
                Head::Basic(AtomParser::translate_pairs(pair.into_inner()))
            }
            internal::Rule::choice_head => {
                Head::Choice(AtomParser::translate_pairs(pair.into_inner()))
            }
            internal::Rule::falsity => Head::Falsity,
            _ => Self::report_unexpected_pair(pair),
        }
    }
}

pub struct BodyParser;

impl PestParser for BodyParser {
    type Node = Body;

    type InternalParser = internal::Parser;
    type Rule = internal::Rule;
    const RULE: Self::Rule = internal::Rule::body_eoi;

    fn translate_pair(pair: pest::iterators::Pair<'_, Self::Rule>) -> Self::Node {
        if pair.as_rule() != internal::Rule::body {
            Self::report_unexpected_pair(pair)
        }

        Body {
            formulas: pair
                .into_inner()
                .map(AtomicFormulaParser::translate_pair)
                .collect(),
        }
    }
}

pub struct RuleParser;

impl PestParser for RuleParser {
    type Node = Rule;

    type InternalParser = internal::Parser;
    type Rule = internal::Rule;
    const RULE: Self::Rule = internal::Rule::rule_eoi;

    fn translate_pair(pair: pest::iterators::Pair<'_, Self::Rule>) -> Self::Node {
        if pair.as_rule() != internal::Rule::rule {
            Self::report_unexpected_pair(pair)
        }

        let mut pairs = pair.into_inner();

        let head = pairs
            .next()
            .map(HeadParser::translate_pair)
            .unwrap_or_else(|| Self::report_missing_pair());
        let body = pairs
            .next()
            .map(BodyParser::translate_pair)
            .unwrap_or_else(|| Body { formulas: vec![] });

        if let Some(pair) = pairs.next() {
            Self::report_unexpected_pair(pair)
        }

        Rule { head, body }
    }
}

pub struct ProgramParser;

impl PestParser for ProgramParser {
    type Node = Program;

    type InternalParser = internal::Parser;
    type Rule = internal::Rule;
    const RULE: Self::Rule = internal::Rule::program_eoi;

    fn translate_pair(pair: pest::iterators::Pair<'_, Self::Rule>) -> Self::Node {
        if pair.as_rule() != internal::Rule::program {
            Self::report_unexpected_pair(pair)
        }

        Program {
            rules: pair.into_inner().map(RuleParser::translate_pair).collect(),
        }
    }
}
#[cfg(test)]
mod tests {
    use {
        super::{
            AggregateAtomParser, AggregateParser, AtomParser, AtomicFormulaParser,
            BinaryOperatorParser, BodyParser, ComparisonParser, HeadParser, LiteralParser,
            PrecomputedTermParser, PredicateParser, ProgramParser, RelationParser, RuleParser,
            SignParser, TermParser, UnaryOperatorParser, VariableParser,
        },
        crate::{
            parsing::TestedParser,
            syntax_tree::asp::{
                Aggregate, AggregateAtom, AggregateOperation, AggregateOrder, Atom, AtomicFormula,
                BinaryOperator, Body, Comparison, Head, Literal, PrecomputedTerm, Predicate,
                Program, Relation, Rule, Sign, Term, UnaryOperator, Variable,
            },
        },
    };

    #[test]
    fn parse_precomputed_term() {
        PrecomputedTermParser
            .should_parse_into([
                ("#inf", PrecomputedTerm::Infimum),
                ("#infimum", PrecomputedTerm::Infimum),
                ("0", PrecomputedTerm::Numeral(0)),
                ("1", PrecomputedTerm::Numeral(1)),
                ("42", PrecomputedTerm::Numeral(42)),
                ("4711", PrecomputedTerm::Numeral(4711)),
                ("-1", PrecomputedTerm::Numeral(-1)),
                ("a", PrecomputedTerm::Symbol("a".into())),
                ("aa", PrecomputedTerm::Symbol("aa".into())),
                ("aA", PrecomputedTerm::Symbol("aA".into())),
                ("_a", PrecomputedTerm::Symbol("_a".into())),
                ("a_", PrecomputedTerm::Symbol("a_".into())),
                ("noto", PrecomputedTerm::Symbol("noto".into())),
                ("#sup", PrecomputedTerm::Supremum),
                ("#supremum", PrecomputedTerm::Supremum),
            ])
            .should_reject([
                "'a",
                "_'x'_'x'_",
                "A",
                "_A",
                "4 2",
                "00",
                "-0",
                "--1",
                "a a",
                "a-a",
                "'",
                "not",
                "#",
                "#infi",
                "#supi",
                "_",
            ]);
    }

    #[test]
    fn parse_variable() {
        VariableParser
            .should_parse_into([
                ("A", Variable("A".into())),
                ("AA", Variable("AA".into())),
                ("Aa", Variable("Aa".into())),
            ])
            .should_reject([
                "_",
                "a",
                "1",
                "A A",
                "A-A",
                "'",
                "-A",
                "_A",
                "'A",
                "_'X'_'X'_",
            ]);
    }

    #[test]
    fn parse_unary_operator() {
        UnaryOperatorParser.should_parse_into([("-", UnaryOperator::Negative)]);
    }

    #[test]
    fn parse_binary_operator() {
        BinaryOperatorParser.should_parse_into([
            ("+", BinaryOperator::Add),
            ("-", BinaryOperator::Subtract),
            ("*", BinaryOperator::Multiply),
            ("/", BinaryOperator::Divide),
            ("\\", BinaryOperator::Modulo),
            ("..", BinaryOperator::Interval),
        ]);
    }

    #[test]
    fn parse_term() {
        TermParser
            .should_parse_into([
                ("#inf", Term::PrecomputedTerm(PrecomputedTerm::Infimum)),
                ("#sup", Term::PrecomputedTerm(PrecomputedTerm::Supremum)),
                ("1", Term::PrecomputedTerm(PrecomputedTerm::Numeral(1))),
                ("(1)", Term::PrecomputedTerm(PrecomputedTerm::Numeral(1))),
                ("-1", Term::PrecomputedTerm(PrecomputedTerm::Numeral(-1))),
                (
                    "-(1)",
                    Term::UnaryOperation {
                        op: UnaryOperator::Negative,
                        arg: Term::PrecomputedTerm(PrecomputedTerm::Numeral(1)).into(),
                    },
                ),
                (
                    "--1",
                    Term::UnaryOperation {
                        op: UnaryOperator::Negative,
                        arg: Term::PrecomputedTerm(PrecomputedTerm::Numeral(-1)).into(),
                    },
                ),
                (
                    "1 + 2",
                    Term::BinaryOperation {
                        op: BinaryOperator::Add,
                        lhs: Term::PrecomputedTerm(PrecomputedTerm::Numeral(1)).into(),
                        rhs: Term::PrecomputedTerm(PrecomputedTerm::Numeral(2)).into(),
                    },
                ),
                (
                    "1..2",
                    Term::BinaryOperation {
                        op: BinaryOperator::Interval,
                        lhs: Term::PrecomputedTerm(PrecomputedTerm::Numeral(1)).into(),
                        rhs: Term::PrecomputedTerm(PrecomputedTerm::Numeral(2)).into(),
                    },
                ),
                (
                    "a",
                    Term::PrecomputedTerm(PrecomputedTerm::Symbol("a".into())),
                ),
                (
                    "(a)",
                    Term::PrecomputedTerm(PrecomputedTerm::Symbol("a".into())),
                ),
                (
                    "-a",
                    Term::UnaryOperation {
                        op: UnaryOperator::Negative,
                        arg: Term::PrecomputedTerm(PrecomputedTerm::Symbol("a".into())).into(),
                    },
                ),
                (
                    "-(a)",
                    Term::UnaryOperation {
                        op: UnaryOperator::Negative,
                        arg: Term::PrecomputedTerm(PrecomputedTerm::Symbol("a".into())).into(),
                    },
                ),
                (
                    "--a",
                    Term::UnaryOperation {
                        op: UnaryOperator::Negative,
                        arg: Term::UnaryOperation {
                            op: UnaryOperator::Negative,
                            arg: Term::PrecomputedTerm(PrecomputedTerm::Symbol("a".into())).into(),
                        }
                        .into(),
                    },
                ),
                (
                    "1 + a",
                    Term::BinaryOperation {
                        op: BinaryOperator::Add,
                        lhs: Term::PrecomputedTerm(PrecomputedTerm::Numeral(1)).into(),
                        rhs: Term::PrecomputedTerm(PrecomputedTerm::Symbol("a".into())).into(),
                    },
                ),
                (
                    "1..a",
                    Term::BinaryOperation {
                        op: BinaryOperator::Interval,
                        lhs: Term::PrecomputedTerm(PrecomputedTerm::Numeral(1)).into(),
                        rhs: Term::PrecomputedTerm(PrecomputedTerm::Symbol("a".into())).into(),
                    },
                ),
                ("A", Term::Variable(Variable("A".into()))),
                ("(A)", Term::Variable(Variable("A".into()))),
                (
                    "-A",
                    Term::UnaryOperation {
                        op: UnaryOperator::Negative,
                        arg: Term::Variable(Variable("A".into())).into(),
                    },
                ),
                (
                    "-(A)",
                    Term::UnaryOperation {
                        op: UnaryOperator::Negative,
                        arg: Term::Variable(Variable("A".into())).into(),
                    },
                ),
                (
                    "--A",
                    Term::UnaryOperation {
                        op: UnaryOperator::Negative,
                        arg: Term::UnaryOperation {
                            op: UnaryOperator::Negative,
                            arg: Term::Variable(Variable("A".into())).into(),
                        }
                        .into(),
                    },
                ),
                (
                    "1 + A",
                    Term::BinaryOperation {
                        op: BinaryOperator::Add,
                        lhs: Term::PrecomputedTerm(PrecomputedTerm::Numeral(1)).into(),
                        rhs: Term::Variable(Variable("A".into())).into(),
                    },
                ),
                (
                    "1..A",
                    Term::BinaryOperation {
                        op: BinaryOperator::Interval,
                        lhs: Term::PrecomputedTerm(PrecomputedTerm::Numeral(1)).into(),
                        rhs: Term::Variable(Variable("A".into())).into(),
                    },
                ),
                (
                    "(1 + A) * (1 - a)",
                    Term::BinaryOperation {
                        op: BinaryOperator::Multiply,
                        lhs: Term::BinaryOperation {
                            op: BinaryOperator::Add,
                            lhs: Term::PrecomputedTerm(PrecomputedTerm::Numeral(1)).into(),
                            rhs: Term::Variable(Variable("A".into())).into(),
                        }
                        .into(),
                        rhs: Term::BinaryOperation {
                            op: BinaryOperator::Subtract,
                            lhs: Term::PrecomputedTerm(PrecomputedTerm::Numeral(1)).into(),
                            rhs: Term::PrecomputedTerm(PrecomputedTerm::Symbol("a".into())).into(),
                        }
                        .into(),
                    },
                ),
                (
                    "((1 + 2) - 3) * 4",
                    Term::BinaryOperation {
                        op: BinaryOperator::Multiply,
                        lhs: Term::BinaryOperation {
                            op: BinaryOperator::Subtract,
                            lhs: Term::BinaryOperation {
                                op: BinaryOperator::Add,
                                lhs: Term::PrecomputedTerm(PrecomputedTerm::Numeral(1)).into(),
                                rhs: Term::PrecomputedTerm(PrecomputedTerm::Numeral(2)).into(),
                            }
                            .into(),
                            rhs: Term::PrecomputedTerm(PrecomputedTerm::Numeral(3)).into(),
                        }
                        .into(),
                        rhs: Term::PrecomputedTerm(PrecomputedTerm::Numeral(4)).into(),
                    },
                ),
                (
                    "2 * (1..3)",
                    Term::BinaryOperation {
                        op: BinaryOperator::Multiply,
                        lhs: Term::PrecomputedTerm(PrecomputedTerm::Numeral(2)).into(),
                        rhs: Term::BinaryOperation {
                            op: BinaryOperator::Interval,
                            lhs: Term::PrecomputedTerm(PrecomputedTerm::Numeral(1)).into(),
                            rhs: Term::PrecomputedTerm(PrecomputedTerm::Numeral(3)).into(),
                        }
                        .into(),
                    },
                ),
                (
                    "1..3..2",
                    Term::BinaryOperation {
                        op: BinaryOperator::Interval,
                        lhs: Term::BinaryOperation {
                            op: BinaryOperator::Interval,
                            lhs: Term::PrecomputedTerm(PrecomputedTerm::Numeral(1)).into(),
                            rhs: Term::PrecomputedTerm(PrecomputedTerm::Numeral(3)).into(),
                        }
                        .into(),
                        rhs: Term::PrecomputedTerm(PrecomputedTerm::Numeral(2)).into(),
                    },
                ),
                (
                    "1 + 2 * 3",
                    Term::BinaryOperation {
                        op: BinaryOperator::Add,
                        lhs: Term::PrecomputedTerm(PrecomputedTerm::Numeral(1)).into(),
                        rhs: Term::BinaryOperation {
                            op: BinaryOperator::Multiply,
                            lhs: Term::PrecomputedTerm(PrecomputedTerm::Numeral(2)).into(),
                            rhs: Term::PrecomputedTerm(PrecomputedTerm::Numeral(3)).into(),
                        }
                        .into(),
                    },
                ),
                (
                    "1 * 2 + 3",
                    Term::BinaryOperation {
                        op: BinaryOperator::Add,
                        lhs: Term::BinaryOperation {
                            op: BinaryOperator::Multiply,
                            lhs: Term::PrecomputedTerm(PrecomputedTerm::Numeral(1)).into(),
                            rhs: Term::PrecomputedTerm(PrecomputedTerm::Numeral(2)).into(),
                        }
                        .into(),
                        rhs: Term::PrecomputedTerm(PrecomputedTerm::Numeral(3)).into(),
                    },
                ),
            ])
            .should_reject([
                "1-",
                "1 +",
                "+ 1",
                "1..",
                "..1",
                "(1 + a",
                "1 + a)",
                "(1 (+ a +) 1)",
            ]);
    }

    #[test]
    fn parse_predicate() {
        PredicateParser
            .should_parse_into([
                (
                    "p/1",
                    Predicate {
                        symbol: "p".into(),
                        arity: 1,
                    },
                ),
                (
                    "p_/1",
                    Predicate {
                        symbol: "p_".into(),
                        arity: 1,
                    },
                ),
                (
                    "_p/1",
                    Predicate {
                        symbol: "_p".into(),
                        arity: 1,
                    },
                ),
            ])
            .should_reject(["p", "1/1", "p/00", "p/01", "_/1", "p/p"]);
    }

    #[test]
    fn parse_atom() {
        AtomParser
            .should_parse_into([
                (
                    "p",
                    Atom {
                        predicate_symbol: "p".into(),
                        terms: vec![],
                    },
                ),
                (
                    "p()",
                    Atom {
                        predicate_symbol: "p".into(),
                        terms: vec![],
                    },
                ),
                (
                    "p(1)",
                    Atom {
                        predicate_symbol: "p".into(),
                        terms: vec![Term::PrecomputedTerm(PrecomputedTerm::Numeral(1))],
                    },
                ),
                (
                    "sqrt_b(1)",
                    Atom {
                        predicate_symbol: "sqrt_b".into(),
                        terms: vec![Term::PrecomputedTerm(PrecomputedTerm::Numeral(1))],
                    },
                ),
                (
                    "p(1, 2)",
                    Atom {
                        predicate_symbol: "p".into(),
                        terms: vec![
                            Term::PrecomputedTerm(PrecomputedTerm::Numeral(1)),
                            Term::PrecomputedTerm(PrecomputedTerm::Numeral(2)),
                        ],
                    },
                ),
            ])
            .should_reject(["p(1,)", "1", "P", "p("]);
    }

    #[test]
    fn parse_sign() {
        SignParser
            .should_parse_into([
                ("", Sign::NoSign),
                ("not", Sign::Negation),
                ("not  not", Sign::DoubleNegation),
            ])
            .should_reject(["notnot", "noto"]);
    }

    #[test]
    fn parse_literal() {
        LiteralParser.should_parse_into([
            (
                "p",
                Literal {
                    sign: Sign::NoSign,
                    atom: Atom {
                        predicate_symbol: "p".into(),
                        terms: vec![],
                    },
                },
            ),
            (
                "not p",
                Literal {
                    sign: Sign::Negation,
                    atom: Atom {
                        predicate_symbol: "p".into(),
                        terms: vec![],
                    },
                },
            ),
            (
                "not not p",
                Literal {
                    sign: Sign::DoubleNegation,
                    atom: Atom {
                        predicate_symbol: "p".into(),
                        terms: vec![],
                    },
                },
            ),
            (
                "notp",
                Literal {
                    sign: Sign::NoSign,
                    atom: Atom {
                        predicate_symbol: "notp".into(),
                        terms: vec![],
                    },
                },
            ),
        ]);
    }

    #[test]
    fn parse_relation() {
        RelationParser
            .should_parse_into([
                ("=", Relation::Equal),
                ("!=", Relation::NotEqual),
                ("<", Relation::Less),
                ("<=", Relation::LessEqual),
                (">", Relation::Greater),
                (">=", Relation::GreaterEqual),
            ])
            .should_reject(["! =", "< =", "> ="]);
    }

    #[test]
    fn parse_comparison() {
        ComparisonParser.should_parse_into([(
            "1 < N",
            Comparison {
                relation: Relation::Less,
                lhs: Term::PrecomputedTerm(PrecomputedTerm::Numeral(1)),
                rhs: Term::Variable(Variable("N".into())),
            },
        )]);
    }

    #[test]
    fn parse_atomic_formula() {
        AtomicFormulaParser.should_parse_into([
            (
                "1 < N",
                AtomicFormula::Comparison(Comparison {
                    relation: Relation::Less,
                    lhs: Term::PrecomputedTerm(PrecomputedTerm::Numeral(1)),
                    rhs: Term::Variable(Variable("N".into())),
                }),
            ),
            (
                "not p",
                AtomicFormula::Literal(Literal {
                    sign: Sign::Negation,
                    atom: Atom {
                        predicate_symbol: "p".into(),
                        terms: vec![],
                    },
                }),
            ),
        ]);
    }

    #[test]
    fn parse_aggregate() {
        AggregateParser.should_parse_into([
            (
                "#count{ X : p(X) }",
                Aggregate {
                    operation: AggregateOperation::Count,
                    variable_list: vec![Variable("X".to_string())],
                    conditions: vec![AtomicFormula::Literal(Literal {
                        sign: Sign::NoSign,
                        atom: Atom {
                            predicate_symbol: "p".into(),
                            terms: vec![Term::Variable(Variable("X".to_string()))],
                        },
                    })],
                },
            ),
            (
                "#count{ X, Y : p(X), X < Y }",
                Aggregate {
                    operation: AggregateOperation::Count,
                    variable_list: vec![Variable("X".to_string()), Variable("Y".to_string())],
                    conditions: vec![
                        AtomicFormula::Literal(Literal {
                            sign: Sign::NoSign,
                            atom: Atom {
                                predicate_symbol: "p".into(),
                                terms: vec![Term::Variable(Variable("X".to_string()))],
                            },
                        }),
                        AtomicFormula::Comparison(Comparison {
                            relation: Relation::Less,
                            lhs: Term::Variable(Variable("X".to_string())),
                            rhs: Term::Variable(Variable("Y".to_string())),
                        }),
                    ],
                },
            ),
        ]);
    }

    #[test]
    fn parse_aggregate_atom() {
        AggregateAtomParser.should_parse_into([
            (
                "#count{ X : p(X) } <= 5",
                AggregateAtom {
                    aggregate: Aggregate {
                        operation: AggregateOperation::Count,
                        variable_list: vec![Variable("X".to_string())],
                        conditions: vec![AtomicFormula::Literal(Literal {
                            sign: Sign::NoSign,
                            atom: Atom {
                                predicate_symbol: "p".into(),
                                terms: vec![Term::Variable(Variable("X".to_string()))],
                            },
                        })],
                    },
                    relation: Relation::LessEqual,
                    guard: Term::PrecomputedTerm(PrecomputedTerm::Numeral(5)),
                    order: AggregateOrder::Left,
                },
            ),
            (
                "0 <= #count{ X, Y : p(X), X < Y }",
                AggregateAtom {
                    aggregate: Aggregate {
                        operation: AggregateOperation::Count,
                        variable_list: vec![Variable("X".to_string()), Variable("Y".to_string())],
                        conditions: vec![
                            AtomicFormula::Literal(Literal {
                                sign: Sign::NoSign,
                                atom: Atom {
                                    predicate_symbol: "p".into(),
                                    terms: vec![Term::Variable(Variable("X".to_string()))],
                                },
                            }),
                            AtomicFormula::Comparison(Comparison {
                                relation: Relation::Less,
                                lhs: Term::Variable(Variable("X".to_string())),
                                rhs: Term::Variable(Variable("Y".to_string())),
                            }),
                        ],
                    },
                    relation: Relation::LessEqual,
                    guard: Term::PrecomputedTerm(PrecomputedTerm::Numeral(0)),
                    order: AggregateOrder::Right,
                },
            ),
        ]);
    }

    #[test]
    fn parse_head() {
        HeadParser.should_parse_into([
            (
                "p",
                Head::Basic(Atom {
                    predicate_symbol: "p".into(),
                    terms: vec![],
                }),
            ),
            (
                "{p}",
                Head::Choice(Atom {
                    predicate_symbol: "p".into(),
                    terms: vec![],
                }),
            ),
            ("", Head::Falsity),
        ]);
    }

    #[test]
    fn parse_body() {
        BodyParser.should_parse_into([
            ("", Body { formulas: vec![] }),
            (
                "p",
                Body {
                    formulas: vec![AtomicFormula::Literal(Literal {
                        sign: Sign::NoSign,
                        atom: Atom {
                            predicate_symbol: "p".into(),
                            terms: vec![],
                        },
                    })],
                },
            ),
            (
                "p, N < 1",
                Body {
                    formulas: vec![
                        AtomicFormula::Literal(Literal {
                            sign: Sign::NoSign,
                            atom: Atom {
                                predicate_symbol: "p".into(),
                                terms: vec![],
                            },
                        }),
                        AtomicFormula::Comparison(Comparison {
                            relation: Relation::Less,
                            lhs: Term::Variable(Variable("N".into())),
                            rhs: Term::PrecomputedTerm(PrecomputedTerm::Numeral(1)),
                        }),
                    ],
                },
            ),
        ]);
    }

    #[test]
    fn parse_rule() {
        RuleParser
            .should_parse_into([
                (
                    ":-.",
                    Rule {
                        head: Head::Falsity,
                        body: Body { formulas: vec![] },
                    },
                ),
                (
                    "a :- b.",
                    Rule {
                        head: Head::Basic(Atom {
                            predicate_symbol: "a".into(),
                            terms: vec![],
                        }),
                        body: Body {
                            formulas: vec![AtomicFormula::Literal(Literal {
                                sign: Sign::NoSign,
                                atom: Atom {
                                    predicate_symbol: "b".into(),
                                    terms: vec![],
                                },
                            })],
                        },
                    },
                ),
                (
                    "p :- a != b.",
                    Rule {
                        head: Head::Basic(Atom {
                            predicate_symbol: "p".into(),
                            terms: vec![],
                        }),
                        body: Body {
                            formulas: vec![AtomicFormula::Comparison(Comparison {
                                lhs: Term::PrecomputedTerm(PrecomputedTerm::Symbol("a".into())),
                                rhs: Term::PrecomputedTerm(PrecomputedTerm::Symbol("b".into())),
                                relation: Relation::NotEqual,
                            })],
                        },
                    },
                ),
                (
                    "a :-.",
                    Rule {
                        head: Head::Basic(Atom {
                            predicate_symbol: "a".into(),
                            terms: vec![],
                        }),
                        body: Body { formulas: vec![] },
                    },
                ),
                (
                    "a.",
                    Rule {
                        head: Head::Basic(Atom {
                            predicate_symbol: "a".into(),
                            terms: vec![],
                        }),
                        body: Body { formulas: vec![] },
                    },
                ),
            ])
            .should_reject(["", "."]);
    }

    #[test]
    fn parse_program() {
        ProgramParser.should_parse_into([
            ("", Program { rules: vec![] }),
            (
                "a. b :- a.",
                Program {
                    rules: vec![
                        Rule {
                            head: Head::Basic(Atom {
                                predicate_symbol: "a".into(),
                                terms: vec![],
                            }),
                            body: Body { formulas: vec![] },
                        },
                        Rule {
                            head: Head::Basic(Atom {
                                predicate_symbol: "b".into(),
                                terms: vec![],
                            }),
                            body: Body {
                                formulas: vec![AtomicFormula::Literal(Literal {
                                    sign: Sign::NoSign,
                                    atom: Atom {
                                        predicate_symbol: "a".into(),
                                        terms: vec![],
                                    },
                                })],
                            },
                        },
                    ],
                },
            ),
            (
                "a.\n",
                Program {
                    rules: vec![Rule {
                        head: Head::Basic(Atom {
                            predicate_symbol: "a".into(),
                            terms: vec![],
                        }),
                        body: Body { formulas: vec![] },
                    }],
                },
            ),
            (
                "% First comment. \na. %%%% Second comment %%%%\n%Last comment",
                Program {
                    rules: vec![Rule {
                        head: Head::Basic(Atom {
                            predicate_symbol: "a".into(),
                            terms: vec![],
                        }),
                        body: Body { formulas: vec![] },
                    }],
                },
            ),
        ]);
    }
}
