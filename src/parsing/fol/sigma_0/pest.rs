use crate::{
    parsing::PestParser,
    syntax_tree::fol::sigma_0::{
        AnnotatedFormula, Atom, AtomicFormula, BinaryConnective, BinaryOperator, Comparison,
        Direction, Formula, FunctionConstant, GeneralTerm, Guard, IntegerTerm,
        PlaceholderDeclaration, Predicate, Quantification, Quantifier, Relation, Role, Sort,
        Specification, SymbolicTerm, Theory, UnaryConnective, UnaryOperator, UserGuide,
        UserGuideEntry, Variable,
    },
};

mod internal {
    use pest::pratt_parser::PrattParser;

    #[derive(pest_derive::Parser)]
    #[grammar = "parsing/fol/sigma_0/grammar.pest"]
    pub struct Parser;

    lazy_static::lazy_static! {
        pub static ref TERM_PRATT_PARSER: PrattParser<Rule> = {
            use pest::pratt_parser::{Assoc::*, Op};
            use Rule::*;

            PrattParser::new()
                .op(Op::infix(add, Left) | Op::infix(subtract, Left))
                .op(Op::infix(multiply, Left))
                .op(Op::prefix(negative))
        };

        pub static ref FORMULA_PRATT_PARSER: PrattParser<Rule> = {
            use pest::pratt_parser::{Assoc::*, Op};
            use Rule::*;

            PrattParser::new()
                .op(Op::infix(equivalence, Right) | Op::infix(implication, Right) | Op::infix(reverse_implication, Left))
                .op(Op::infix(disjunction, Left))
                .op(Op::infix(conjunction, Left))
                .op(Op::prefix(negation) | Op::prefix(quantification))
        };
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
            _ => Self::report_unexpected_pair(pair),
        }
    }
}

pub struct IntegerTermParser;

impl PestParser for IntegerTermParser {
    type Node = IntegerTerm;

    type InternalParser = internal::Parser;
    type Rule = internal::Rule;
    const RULE: internal::Rule = internal::Rule::integer_term_eoi;

    fn translate_pair(pair: pest::iterators::Pair<'_, Self::Rule>) -> Self::Node {
        internal::TERM_PRATT_PARSER
            .map_primary(|primary| match primary.as_rule() {
                internal::Rule::integer_term => IntegerTermParser::translate_pair(primary),
                internal::Rule::numeral => IntegerTerm::Numeral(primary.as_str().parse().unwrap()),
                internal::Rule::integer_function_constant => match primary.into_inner().next() {
                    Some(pair) if pair.as_rule() == internal::Rule::symbolic_constant => {
                        IntegerTerm::FunctionConstant(pair.as_str().into())
                    }
                    Some(pair) => Self::report_unexpected_pair(pair),
                    None => Self::report_missing_pair(),
                },
                internal::Rule::integer_variable => match primary.into_inner().next() {
                    Some(pair) if pair.as_rule() == internal::Rule::unsorted_variable => {
                        IntegerTerm::Variable(pair.as_str().into())
                    }
                    Some(pair) => Self::report_unexpected_pair(pair),
                    None => Self::report_missing_pair(),
                },
                _ => Self::report_unexpected_pair(primary),
            })
            .map_prefix(|op, arg| IntegerTerm::UnaryOperation {
                op: UnaryOperatorParser::translate_pair(op),
                arg: Box::new(arg),
            })
            .map_infix(|lhs, op, rhs| IntegerTerm::BinaryOperation {
                op: BinaryOperatorParser::translate_pair(op),
                lhs: Box::new(lhs),
                rhs: Box::new(rhs),
            })
            .parse(pair.into_inner())
    }
}

pub struct SymbolicTermParser;

impl PestParser for SymbolicTermParser {
    type Node = SymbolicTerm;

    type InternalParser = internal::Parser;
    type Rule = internal::Rule;
    const RULE: internal::Rule = internal::Rule::symbolic_term_eoi;

    fn translate_pair(pair: pest::iterators::Pair<'_, Self::Rule>) -> Self::Node {
        match pair.as_rule() {
            internal::Rule::symbolic_term => Self::translate_pairs(pair.into_inner()),
            internal::Rule::symbolic_constant => SymbolicTerm::Symbol(pair.as_str().into()),
            internal::Rule::symbolic_function_constant => match pair.into_inner().next() {
                Some(pair) if pair.as_rule() == internal::Rule::symbolic_constant => {
                    SymbolicTerm::FunctionConstant(pair.as_str().into())
                }
                Some(pair) => Self::report_unexpected_pair(pair),
                None => Self::report_missing_pair(),
            },
            internal::Rule::symbolic_variable => match pair.into_inner().next() {
                Some(pair) if pair.as_rule() == internal::Rule::unsorted_variable => {
                    SymbolicTerm::Variable(pair.as_str().into())
                }
                Some(pair) => Self::report_unexpected_pair(pair),
                None => Self::report_missing_pair(),
            },
            _ => Self::report_unexpected_pair(pair),
        }
    }
}

pub struct GeneralTermParser;

impl PestParser for GeneralTermParser {
    type Node = GeneralTerm;

    type InternalParser = internal::Parser;
    type Rule = internal::Rule;
    const RULE: internal::Rule = internal::Rule::general_term_eoi;

    fn translate_pair(pair: pest::iterators::Pair<'_, Self::Rule>) -> Self::Node {
        match pair.as_rule() {
            internal::Rule::general_term => Self::translate_pairs(pair.into_inner()),
            internal::Rule::infimum => GeneralTerm::Infimum,
            internal::Rule::supremum => GeneralTerm::Supremum,
            internal::Rule::general_function_constant => match pair.into_inner().next() {
                Some(pair) if pair.as_rule() == internal::Rule::symbolic_constant => {
                    GeneralTerm::FunctionConstant(pair.as_str().into())
                }
                Some(pair) => Self::report_unexpected_pair(pair),
                None => Self::report_missing_pair(),
            },
            internal::Rule::general_variable => match pair.into_inner().next() {
                Some(pair) if pair.as_rule() == internal::Rule::unsorted_variable => {
                    GeneralTerm::Variable(pair.as_str().into())
                }
                Some(pair) => Self::report_unexpected_pair(pair),
                None => Self::report_missing_pair(),
            },
            internal::Rule::integer_term => {
                GeneralTerm::IntegerTerm(IntegerTermParser::translate_pair(pair))
            }
            internal::Rule::symbolic_term => {
                GeneralTerm::SymbolicTerm(SymbolicTermParser::translate_pair(pair))
            }
            _ => Self::report_unexpected_pair(pair),
        }
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

        let predicate_symbol = pairs
            .next()
            .unwrap_or_else(|| Self::report_missing_pair())
            .as_str()
            .into();
        let terms: Vec<_> = pairs.map(GeneralTermParser::translate_pair).collect();

        Atom {
            predicate_symbol,
            terms,
        }
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
            internal::Rule::relation => Self::translate_pairs(pair.into_inner()),
            internal::Rule::greater_equal => Relation::GreaterEqual,
            internal::Rule::less_equal => Relation::LessEqual,
            internal::Rule::greater => Relation::Greater,
            internal::Rule::less => Relation::Less,
            internal::Rule::equal => Relation::Equal,
            internal::Rule::not_equal => Relation::NotEqual,
            _ => Self::report_unexpected_pair(pair),
        }
    }
}

pub struct GuardParser;

impl PestParser for GuardParser {
    type Node = Guard;

    type InternalParser = internal::Parser;
    type Rule = internal::Rule;
    const RULE: Self::Rule = internal::Rule::guard_eoi;

    fn translate_pair(pair: pest::iterators::Pair<'_, Self::Rule>) -> Self::Node {
        if pair.as_rule() != internal::Rule::guard {
            Self::report_unexpected_pair(pair)
        }

        let mut pairs = pair.into_inner();

        let relation = RelationParser::translate_pair(
            pairs.next().unwrap_or_else(|| Self::report_missing_pair()),
        );
        let term = GeneralTermParser::translate_pair(
            pairs.next().unwrap_or_else(|| Self::report_missing_pair()),
        );

        if let Some(pair) = pairs.next() {
            Self::report_unexpected_pair(pair)
        }

        Guard { relation, term }
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

        let term = GeneralTermParser::translate_pair(
            pairs.next().unwrap_or_else(|| Self::report_missing_pair()),
        );

        let guards: Vec<_> = pairs.map(GuardParser::translate_pair).collect();

        Comparison { term, guards }
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
            internal::Rule::truth => AtomicFormula::Truth,
            internal::Rule::falsity => AtomicFormula::Falsity,
            internal::Rule::atom => AtomicFormula::Atom(AtomParser::translate_pair(pair)),
            internal::Rule::comparison => {
                AtomicFormula::Comparison(ComparisonParser::translate_pair(pair))
            }
            _ => Self::report_unexpected_pair(pair),
        }
    }
}

pub struct QuantifierParser;

impl PestParser for QuantifierParser {
    type Node = Quantifier;

    type InternalParser = internal::Parser;
    type Rule = internal::Rule;
    const RULE: internal::Rule = internal::Rule::quantifier_eoi;

    fn translate_pair(pair: pest::iterators::Pair<'_, Self::Rule>) -> Self::Node {
        match pair.as_rule() {
            internal::Rule::quantifier => QuantifierParser::translate_pairs(pair.into_inner()),
            internal::Rule::forall => Quantifier::Forall,
            internal::Rule::exists => Quantifier::Exists,
            _ => Self::report_unexpected_pair(pair),
        }
    }
}

pub struct FunctionConstantParser;

impl PestParser for FunctionConstantParser {
    type Node = FunctionConstant;

    type InternalParser = internal::Parser;
    type Rule = internal::Rule;
    const RULE: internal::Rule = internal::Rule::function_constant_eoi;

    fn translate_pair(pair: pest::iterators::Pair<'_, Self::Rule>) -> Self::Node {
        match pair.as_rule() {
            internal::Rule::function_constant => {
                FunctionConstantParser::translate_pairs(pair.into_inner())
            }
            internal::Rule::integer_function_constant => match pair.into_inner().next() {
                Some(pair) if pair.as_rule() == internal::Rule::symbolic_constant => {
                    FunctionConstant {
                        name: pair.as_str().into(),
                        sort: Sort::Integer,
                    }
                }
                Some(pair) => Self::report_unexpected_pair(pair),
                None => Self::report_missing_pair(),
            },
            internal::Rule::symbolic_function_constant => match pair.into_inner().next() {
                Some(pair) if pair.as_rule() == internal::Rule::symbolic_constant => {
                    FunctionConstant {
                        name: pair.as_str().into(),
                        sort: Sort::Symbol,
                    }
                }
                Some(pair) => Self::report_unexpected_pair(pair),
                None => Self::report_missing_pair(),
            },
            internal::Rule::general_function_constant => match pair.into_inner().next() {
                Some(pair) if pair.as_rule() == internal::Rule::symbolic_constant => {
                    FunctionConstant {
                        name: pair.as_str().into(),
                        sort: Sort::General,
                    }
                }
                Some(pair) => Self::report_unexpected_pair(pair),
                None => Self::report_missing_pair(),
            },
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
        match pair.as_rule() {
            internal::Rule::variable => VariableParser::translate_pairs(pair.into_inner()),
            internal::Rule::integer_variable => match pair.into_inner().next() {
                Some(pair) if pair.as_rule() == internal::Rule::unsorted_variable => Variable {
                    name: pair.as_str().into(),
                    sort: Sort::Integer,
                },
                Some(pair) => Self::report_unexpected_pair(pair),
                None => Self::report_missing_pair(),
            },
            internal::Rule::symbolic_variable => match pair.into_inner().next() {
                Some(pair) if pair.as_rule() == internal::Rule::unsorted_variable => Variable {
                    name: pair.as_str().into(),
                    sort: Sort::Symbol,
                },
                Some(pair) => Self::report_unexpected_pair(pair),
                None => Self::report_missing_pair(),
            },
            internal::Rule::general_variable => match pair.into_inner().next() {
                Some(pair) if pair.as_rule() == internal::Rule::unsorted_variable => Variable {
                    name: pair.as_str().into(),
                    sort: Sort::General,
                },
                Some(pair) => Self::report_unexpected_pair(pair),
                None => Self::report_missing_pair(),
            },
            _ => Self::report_unexpected_pair(pair),
        }
    }
}

pub struct QuantificationParser;

impl PestParser for QuantificationParser {
    type Node = Quantification;

    type InternalParser = internal::Parser;
    type Rule = internal::Rule;
    const RULE: internal::Rule = internal::Rule::quantification_eoi;

    fn translate_pair(pair: pest::iterators::Pair<'_, Self::Rule>) -> Self::Node {
        if pair.as_rule() != internal::Rule::quantification {
            Self::report_unexpected_pair(pair)
        }

        let mut pairs = pair.into_inner();

        let quantifier = QuantifierParser::translate_pair(
            pairs.next().unwrap_or_else(|| Self::report_missing_pair()),
        );

        let variables: Vec<_> = pairs.map(VariableParser::translate_pair).collect();

        Quantification {
            quantifier,
            variables,
        }
    }
}

pub struct SortParser;

impl PestParser for SortParser {
    type Node = Sort;

    type InternalParser = internal::Parser;
    type Rule = internal::Rule;
    const RULE: internal::Rule = internal::Rule::sort_eoi;

    fn translate_pair(pair: pest::iterators::Pair<'_, Self::Rule>) -> Self::Node {
        match pair.as_rule() {
            internal::Rule::sort => Self::translate_pairs(pair.into_inner()),
            internal::Rule::general_sort => Sort::General,
            internal::Rule::symbolic_sort => Sort::Symbol,
            internal::Rule::integer_sort => Sort::Integer,
            _ => Self::report_unexpected_pair(pair),
        }
    }
}

pub struct UnaryConnectiveParser;

impl PestParser for UnaryConnectiveParser {
    type Node = UnaryConnective;

    type InternalParser = internal::Parser;
    type Rule = internal::Rule;
    const RULE: internal::Rule = internal::Rule::unary_connective_eoi;

    fn translate_pair(pair: pest::iterators::Pair<'_, Self::Rule>) -> Self::Node {
        match pair.as_rule() {
            internal::Rule::negation => UnaryConnective::Negation,
            _ => Self::report_unexpected_pair(pair),
        }
    }
}

pub struct BinaryConnectiveParser;

impl PestParser for BinaryConnectiveParser {
    type Node = BinaryConnective;

    type InternalParser = internal::Parser;
    type Rule = internal::Rule;
    const RULE: internal::Rule = internal::Rule::binary_connective_eoi;

    fn translate_pair(pair: pest::iterators::Pair<'_, Self::Rule>) -> Self::Node {
        match pair.as_rule() {
            internal::Rule::binary_connective => Self::translate_pairs(pair.into_inner()),
            internal::Rule::equivalence => BinaryConnective::Equivalence,
            internal::Rule::implication => BinaryConnective::Implication,
            internal::Rule::reverse_implication => BinaryConnective::ReverseImplication,
            internal::Rule::conjunction => BinaryConnective::Conjunction,
            internal::Rule::disjunction => BinaryConnective::Disjunction,
            _ => Self::report_unexpected_pair(pair),
        }
    }
}

pub struct FormulaParser;

impl PestParser for FormulaParser {
    type Node = Formula;

    type InternalParser = internal::Parser;
    type Rule = internal::Rule;
    const RULE: Self::Rule = internal::Rule::formula_eoi;

    fn translate_pair(pair: pest::iterators::Pair<'_, Self::Rule>) -> Self::Node {
        internal::FORMULA_PRATT_PARSER
            .map_primary(|primary| match primary.as_rule() {
                internal::Rule::formula => FormulaParser::translate_pair(primary),
                internal::Rule::atomic_formula => {
                    Formula::AtomicFormula(AtomicFormulaParser::translate_pair(primary))
                }
                _ => Self::report_unexpected_pair(primary),
            })
            .map_prefix(|op, arg| match op.as_rule() {
                internal::Rule::quantification => Formula::QuantifiedFormula {
                    quantification: QuantificationParser::translate_pair(op),
                    formula: Box::new(arg),
                },
                internal::Rule::negation => Formula::UnaryFormula {
                    connective: UnaryConnective::Negation,
                    formula: Box::new(arg),
                },
                _ => Self::report_unexpected_pair(op),
            })
            .map_infix(|lhs, op, rhs| Formula::BinaryFormula {
                connective: BinaryConnectiveParser::translate_pair(op),
                lhs: Box::new(lhs),
                rhs: Box::new(rhs),
            })
            .parse(pair.into_inner())
    }
}

pub struct TheoryParser;

impl PestParser for TheoryParser {
    type Node = Theory;

    type InternalParser = internal::Parser;
    type Rule = internal::Rule;
    const RULE: Self::Rule = internal::Rule::theory_eoi;

    fn translate_pair(pair: pest::iterators::Pair<'_, Self::Rule>) -> Self::Node {
        if pair.as_rule() != internal::Rule::theory {
            Self::report_unexpected_pair(pair)
        }
        Theory {
            formulas: pair
                .into_inner()
                .map(FormulaParser::translate_pair)
                .collect(),
        }
    }
}

pub struct RoleParser;

impl PestParser for RoleParser {
    type Node = Role;

    type InternalParser = internal::Parser;
    type Rule = internal::Rule;
    const RULE: internal::Rule = internal::Rule::role_eoi;

    fn translate_pair(pair: pest::iterators::Pair<'_, Self::Rule>) -> Self::Node {
        match pair.as_rule() {
            internal::Rule::role => Self::translate_pairs(pair.into_inner()),
            internal::Rule::assumption => Role::Assumption,
            internal::Rule::spec => Role::Spec,
            internal::Rule::lemma => Role::Lemma,
            internal::Rule::definition => Role::Definition,
            internal::Rule::inductive_lemma => Role::InductiveLemma,
            _ => Self::report_unexpected_pair(pair),
        }
    }
}

pub struct DirectionParser;

impl PestParser for DirectionParser {
    type Node = Direction;

    type InternalParser = internal::Parser;
    type Rule = internal::Rule;
    const RULE: internal::Rule = internal::Rule::direction_eoi;

    fn translate_pair(pair: pest::iterators::Pair<'_, Self::Rule>) -> Self::Node {
        match pair.as_rule() {
            internal::Rule::direction => Self::translate_pairs(pair.into_inner()),
            internal::Rule::universal => Direction::Universal,
            internal::Rule::forward => Direction::Forward,
            internal::Rule::backward => Direction::Backward,
            _ => Self::report_unexpected_pair(pair),
        }
    }
}

pub struct AnnotatedFormulaParser;

impl PestParser for AnnotatedFormulaParser {
    type Node = AnnotatedFormula;

    type InternalParser = internal::Parser;
    type Rule = internal::Rule;
    const RULE: internal::Rule = internal::Rule::annotated_formula_eoi;

    fn translate_pair(pair: pest::iterators::Pair<'_, Self::Rule>) -> Self::Node {
        if pair.as_rule() != internal::Rule::annotated_formula {
            Self::report_unexpected_pair(pair)
        }

        let mut pairs = pair.into_inner();
        let mut next = pairs.next().unwrap_or_else(|| Self::report_missing_pair());

        let role = RoleParser::translate_pair(next);
        next = pairs.next().unwrap_or_else(|| Self::report_missing_pair());

        let direction;
        if matches!(next.as_rule(), internal::Rule::direction) {
            direction = DirectionParser::translate_pair(next);
            next = pairs.next().unwrap_or_else(|| Self::report_missing_pair());
        } else {
            direction = Direction::default()
        }

        let name;
        if matches!(next.as_rule(), internal::Rule::symbolic_constant) {
            name = next.as_str().into();
            next = pairs.next().unwrap_or_else(|| Self::report_missing_pair());
        } else {
            name = String::default();
        }

        let formula = FormulaParser::translate_pair(next);

        if let Some(pair) = pairs.next() {
            Self::report_unexpected_pair(pair)
        }

        AnnotatedFormula {
            role,
            direction,
            name,
            formula,
        }
    }
}

pub struct SpecificationParser;

impl PestParser for SpecificationParser {
    type Node = Specification;

    type InternalParser = internal::Parser;
    type Rule = internal::Rule;
    const RULE: internal::Rule = internal::Rule::specification_eoi;

    fn translate_pair(pair: pest::iterators::Pair<'_, Self::Rule>) -> Self::Node {
        if pair.as_rule() != internal::Rule::specification {
            Self::report_unexpected_pair(pair)
        }
        Specification {
            formulas: pair
                .into_inner()
                .map(AnnotatedFormulaParser::translate_pair)
                .collect(),
        }
    }
}

pub struct PlaceholderDeclarationParser;

impl PestParser for PlaceholderDeclarationParser {
    type Node = PlaceholderDeclaration;

    type InternalParser = internal::Parser;
    type Rule = internal::Rule;
    const RULE: internal::Rule = internal::Rule::placeholder_declaration;

    fn translate_pair(pair: pest::iterators::Pair<'_, Self::Rule>) -> Self::Node {
        if pair.as_rule() != internal::Rule::placeholder_declaration {
            Self::report_unexpected_pair(pair)
        }

        let mut pairs = pair.into_inner();

        let name = pairs
            .next()
            .unwrap_or_else(|| Self::report_missing_pair())
            .as_str()
            .into();

        let sort = pairs
            .next()
            .map(SortParser::translate_pair)
            .unwrap_or_else(|| Sort::General);

        if let Some(pair) = pairs.next() {
            Self::report_unexpected_pair(pair)
        }

        PlaceholderDeclaration { name, sort }
    }
}

pub struct UserGuideEntryParser;

impl PestParser for UserGuideEntryParser {
    type Node = UserGuideEntry;

    type InternalParser = internal::Parser;
    type Rule = internal::Rule;
    const RULE: internal::Rule = internal::Rule::user_guide_entry_eoi;

    fn translate_pair(pair: pest::iterators::Pair<'_, Self::Rule>) -> Self::Node {
        match pair.as_rule() {
            internal::Rule::user_guide_entry => Self::translate_pairs(pair.into_inner()),
            internal::Rule::input_predicate => {
                UserGuideEntry::InputPredicate(PredicateParser::translate_pairs(pair.into_inner()))
            }
            internal::Rule::output_predicate => {
                UserGuideEntry::OutputPredicate(PredicateParser::translate_pairs(pair.into_inner()))
            }
            internal::Rule::placeholder_declaration => UserGuideEntry::PlaceholderDeclaration(
                PlaceholderDeclarationParser::translate_pair(pair),
            ),
            internal::Rule::annotated_formula => {
                UserGuideEntry::AnnotatedFormula(AnnotatedFormulaParser::translate_pair(pair))
            }
            _ => Self::report_unexpected_pair(pair),
        }
    }
}

pub struct UserGuideParser;

impl PestParser for UserGuideParser {
    type Node = UserGuide;

    type InternalParser = internal::Parser;
    type Rule = internal::Rule;
    const RULE: internal::Rule = internal::Rule::user_guide_eoi;

    fn translate_pair(pair: pest::iterators::Pair<'_, Self::Rule>) -> Self::Node {
        if pair.as_rule() != internal::Rule::user_guide {
            Self::report_unexpected_pair(pair)
        }
        UserGuide {
            entries: pair
                .into_inner()
                .map(UserGuideEntryParser::translate_pair)
                .collect(),
        }
    }
}

#[cfg(test)]
mod tests {
    use {
        super::{
            AnnotatedFormulaParser, AtomParser, AtomicFormulaParser, BinaryConnectiveParser,
            BinaryOperatorParser, ComparisonParser, DirectionParser, FormulaParser,
            GeneralTermParser, GuardParser, IntegerTermParser, PredicateParser,
            QuantificationParser, QuantifierParser, RelationParser, RoleParser, SortParser,
            SpecificationParser, SymbolicTermParser, TheoryParser, UnaryConnectiveParser,
            UnaryOperatorParser, UserGuideEntryParser, UserGuideParser, VariableParser,
        },
        crate::{
            parsing::TestedParser,
            syntax_tree::fol::sigma_0::{
                AnnotatedFormula, Atom, AtomicFormula, BinaryConnective, BinaryOperator,
                Comparison, Direction, Formula, GeneralTerm, Guard, IntegerTerm,
                PlaceholderDeclaration, Predicate, Quantification, Quantifier, Relation, Role,
                Sort, Specification, SymbolicTerm, Theory, UnaryConnective, UnaryOperator,
                UserGuide, UserGuideEntry, Variable,
            },
        },
        std::vec,
    };

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
        ]);
    }

    #[test]
    fn parse_integer_term() {
        IntegerTermParser
            .should_parse_into([
                ("0", IntegerTerm::Numeral(0)),
                ("1", IntegerTerm::Numeral(1)),
                ("-1", IntegerTerm::Numeral(-1)),
                ("-48", IntegerTerm::Numeral(-48)),
                ("(-48)", IntegerTerm::Numeral(-48)),
                ("a$i", IntegerTerm::FunctionConstant("a".into())),
                ("X$i", IntegerTerm::Variable("X".into())),
                ("Xvar$", IntegerTerm::Variable("Xvar".into())),
                (
                    "-X$i",
                    IntegerTerm::UnaryOperation {
                        op: UnaryOperator::Negative,
                        arg: IntegerTerm::Variable("X".into()).into(),
                    },
                ),
                ("301", IntegerTerm::Numeral(301)),
                ("(301)", IntegerTerm::Numeral(301)),
                (
                    "1 + 3 + 2",
                    IntegerTerm::BinaryOperation {
                        op: BinaryOperator::Add,
                        lhs: IntegerTerm::BinaryOperation {
                            op: BinaryOperator::Add,
                            lhs: IntegerTerm::Numeral(1).into(),
                            rhs: IntegerTerm::Numeral(3).into(),
                        }
                        .into(),
                        rhs: IntegerTerm::Numeral(2).into(),
                    },
                ),
            ])
            .should_reject([
                "00", "#", "#inf", "#infi", "#sup", "#supa", "_", "1_", "(1", "X", "X$s", "X$g",
            ]);
    }

    #[test]
    fn parse_symbolic_terms() {
        SymbolicTermParser
            .should_parse_into([
                ("a", SymbolicTerm::Symbol("a".into())),
                ("a$s", SymbolicTerm::FunctionConstant("a".into())),
                ("X$s", SymbolicTerm::Variable("X".into())),
            ])
            .should_reject(["0", "a$i", "a$g", "X$i", "X$g"]);
    }

    #[test]
    fn parse_general_term() {
        GeneralTermParser
            .should_parse_into([
                ("#inf", GeneralTerm::Infimum),
                ("#sup", GeneralTerm::Supremum),
                ("a$g", GeneralTerm::FunctionConstant("a".into())),
                ("1", GeneralTerm::IntegerTerm(IntegerTerm::Numeral(1))),
                ("(1)", GeneralTerm::IntegerTerm(IntegerTerm::Numeral(1))),
                ("-1", GeneralTerm::IntegerTerm(IntegerTerm::Numeral(-1))),
                (
                    "-(1)",
                    GeneralTerm::IntegerTerm(IntegerTerm::UnaryOperation {
                        op: UnaryOperator::Negative,
                        arg: IntegerTerm::Numeral(1).into(),
                    }),
                ),
                (
                    "--1",
                    GeneralTerm::IntegerTerm(IntegerTerm::UnaryOperation {
                        op: UnaryOperator::Negative,
                        arg: IntegerTerm::Numeral(-1).into(),
                    }),
                ),
                (
                    "1 + 2",
                    GeneralTerm::IntegerTerm(IntegerTerm::BinaryOperation {
                        op: BinaryOperator::Add,
                        lhs: IntegerTerm::Numeral(1).into(),
                        rhs: IntegerTerm::Numeral(2).into(),
                    }),
                ),
                (
                    "a",
                    GeneralTerm::SymbolicTerm(SymbolicTerm::Symbol("a".into())),
                ),
                (
                    "ca_12",
                    GeneralTerm::SymbolicTerm(SymbolicTerm::Symbol("ca_12".into())),
                ),
                (
                    "_b12A",
                    GeneralTerm::SymbolicTerm(SymbolicTerm::Symbol("_b12A".into())),
                ),
                ("A", GeneralTerm::Variable("A".into())),
                (
                    "1 + A$i",
                    GeneralTerm::IntegerTerm(IntegerTerm::BinaryOperation {
                        op: BinaryOperator::Add,
                        lhs: IntegerTerm::Numeral(1).into(),
                        rhs: IntegerTerm::Variable("A".into()).into(),
                    }),
                ),
                (
                    "(1 + Nx$i) * (Y$i - B1$i)",
                    GeneralTerm::IntegerTerm(IntegerTerm::BinaryOperation {
                        op: BinaryOperator::Multiply,
                        lhs: IntegerTerm::BinaryOperation {
                            op: BinaryOperator::Add,
                            lhs: IntegerTerm::Numeral(1).into(),
                            rhs: IntegerTerm::Variable("Nx".into()).into(),
                        }
                        .into(),
                        rhs: IntegerTerm::BinaryOperation {
                            op: BinaryOperator::Subtract,
                            lhs: IntegerTerm::Variable("Y".into()).into(),
                            rhs: IntegerTerm::Variable("B1".into()).into(),
                        }
                        .into(),
                    }),
                ),
                (
                    "((1 + 2) - -3) * 4",
                    GeneralTerm::IntegerTerm(IntegerTerm::BinaryOperation {
                        op: BinaryOperator::Multiply,
                        lhs: IntegerTerm::BinaryOperation {
                            op: BinaryOperator::Subtract,
                            lhs: IntegerTerm::BinaryOperation {
                                op: BinaryOperator::Add,
                                lhs: IntegerTerm::Numeral(1).into(),
                                rhs: IntegerTerm::Numeral(2).into(),
                            }
                            .into(),
                            rhs: IntegerTerm::Numeral(-3).into(),
                        }
                        .into(),
                        rhs: IntegerTerm::Numeral(4).into(),
                    }),
                ),
                (
                    "1 + 2 * 3",
                    GeneralTerm::IntegerTerm(IntegerTerm::BinaryOperation {
                        op: BinaryOperator::Add,
                        lhs: IntegerTerm::Numeral(1).into(),
                        rhs: IntegerTerm::BinaryOperation {
                            op: BinaryOperator::Multiply,
                            lhs: IntegerTerm::Numeral(2).into(),
                            rhs: IntegerTerm::Numeral(3).into(),
                        }
                        .into(),
                    }),
                ),
                (
                    "1 * 2 + 3",
                    GeneralTerm::IntegerTerm(IntegerTerm::BinaryOperation {
                        op: BinaryOperator::Add,
                        lhs: IntegerTerm::BinaryOperation {
                            op: BinaryOperator::Multiply,
                            lhs: IntegerTerm::Numeral(1).into(),
                            rhs: IntegerTerm::Numeral(2).into(),
                        }
                        .into(),
                        rhs: IntegerTerm::Numeral(3).into(),
                    }),
                ),
            ])
            .should_reject([
                "(a)",
                "-a",
                "(A)",
                "1 + A",
                "1 + a",
                "1-",
                "1 +",
                "+1",
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
                    // Parsing "g" caused issues ealier because "g" is also a sort declaration.
                    "g",
                    Atom {
                        predicate_symbol: "g".into(),
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
                        terms: vec![GeneralTerm::IntegerTerm(IntegerTerm::Numeral(1))],
                    },
                ),
                (
                    "p(1, 2)",
                    Atom {
                        predicate_symbol: "p".into(),
                        terms: vec![
                            GeneralTerm::IntegerTerm(IntegerTerm::Numeral(1)),
                            GeneralTerm::IntegerTerm(IntegerTerm::Numeral(2)),
                        ],
                    },
                ),
                (
                    "p(X, a)",
                    Atom {
                        predicate_symbol: "p".into(),
                        terms: vec![
                            GeneralTerm::Variable("X".into()),
                            GeneralTerm::SymbolicTerm(SymbolicTerm::Symbol("a".into())),
                        ],
                    },
                ),
            ])
            .should_reject(["p(1,)", "1", "P", "p("]);
    }

    #[test]
    fn parse_relation() {
        RelationParser
            .should_parse_into([
                ("<", Relation::Less),
                (">", Relation::Greater),
                ("<=", Relation::LessEqual),
                (">=", Relation::GreaterEqual),
                ("!=", Relation::NotEqual),
                ("=", Relation::Equal),
            ])
            .should_reject(["< =", "< =", "less"]);
    }

    #[test]
    fn parse_guard() {
        GuardParser
            .should_parse_into([(
                "< N$g",
                Guard {
                    relation: Relation::Less,
                    term: GeneralTerm::Variable("N".into()),
                },
            )])
            .should_reject(["< 3 =", "="]);
    }

    #[test]
    fn parse_binary_connective() {
        BinaryConnectiveParser
            .should_parse_into([
                ("and", BinaryConnective::Conjunction),
                ("or", BinaryConnective::Disjunction),
                ("->", BinaryConnective::Implication),
                ("<-", BinaryConnective::ReverseImplication),
                ("<->", BinaryConnective::Equivalence),
            ])
            .should_reject(["<=", "< ->", "<- >", "anda", "And", "o r"]);
    }

    #[test]
    fn parse_comparison() {
        ComparisonParser
            .should_parse_into([(
                "p < 5",
                Comparison {
                    term: GeneralTerm::SymbolicTerm(SymbolicTerm::Symbol("p".into())),
                    guards: vec![Guard {
                        relation: Relation::Less,
                        term: GeneralTerm::IntegerTerm(IntegerTerm::Numeral(5)),
                    }],
                },
            )])
            .should_reject(["A < B < "]);
    }

    #[test]
    fn parse_atomic_formula() {
        AtomicFormulaParser
            .should_parse_into([
                ("#true", AtomicFormula::Truth),
                ("#false", AtomicFormula::Falsity),
                (
                    "1 = N$g",
                    AtomicFormula::Comparison(Comparison {
                        term: GeneralTerm::IntegerTerm(IntegerTerm::Numeral(1)),
                        guards: vec![Guard {
                            relation: Relation::Equal,
                            term: GeneralTerm::Variable("N".into()),
                        }],
                    }),
                ),
                (
                    "1 = N$",
                    AtomicFormula::Comparison(Comparison {
                        term: GeneralTerm::IntegerTerm(IntegerTerm::Numeral(1)),
                        guards: vec![Guard {
                            relation: Relation::Equal,
                            term: GeneralTerm::IntegerTerm(IntegerTerm::Variable("N".into())),
                        }],
                    }),
                ),
                (
                    "n > 1",
                    AtomicFormula::Comparison(Comparison {
                        term: GeneralTerm::SymbolicTerm(SymbolicTerm::Symbol("n".to_string())),
                        guards: vec![Guard {
                            relation: Relation::Greater,
                            term: GeneralTerm::IntegerTerm(IntegerTerm::Numeral(1)),
                        }],
                    }),
                ),
                (
                    "1 <= N$g > 3 < X$i",
                    AtomicFormula::Comparison(Comparison {
                        term: GeneralTerm::IntegerTerm(IntegerTerm::Numeral(1)),
                        guards: vec![
                            Guard {
                                relation: Relation::LessEqual,
                                term: GeneralTerm::Variable("N".into()),
                            },
                            Guard {
                                relation: Relation::Greater,
                                term: GeneralTerm::IntegerTerm(IntegerTerm::Numeral(3)),
                            },
                            Guard {
                                relation: Relation::Less,
                                term: GeneralTerm::IntegerTerm(IntegerTerm::Variable("X".into())),
                            },
                        ],
                    }),
                ),
                (
                    "p(N$i, 3*2)",
                    AtomicFormula::Atom(Atom {
                        predicate_symbol: "p".into(),
                        terms: vec![
                            GeneralTerm::IntegerTerm(IntegerTerm::Variable("N".into())),
                            GeneralTerm::IntegerTerm(IntegerTerm::BinaryOperation {
                                op: BinaryOperator::Multiply,
                                lhs: IntegerTerm::Numeral(3).into(),
                                rhs: IntegerTerm::Numeral(2).into(),
                            }),
                        ],
                    }),
                ),
            ])
            .should_reject(["p and b"]);
    }

    #[test]
    fn parse_sort() {
        SortParser
            .should_parse_into([
                ("i", Sort::Integer),
                ("integer", Sort::Integer),
                ("s", Sort::Symbol),
                ("symbol", Sort::Symbol),
                ("g", Sort::General),
                ("general", Sort::General),
            ])
            .should_reject(["int", "sym", "gen"]);
    }

    #[test]
    fn parse_unary_connective() {
        UnaryConnectiveParser
            .should_parse_into([("not", UnaryConnective::Negation)])
            .should_reject(["noto", "not(", "n ot"]);
    }

    #[test]
    fn parse_quantifier() {
        QuantifierParser
            .should_parse_into([
                ("forall", Quantifier::Forall),
                ("exists", Quantifier::Exists),
            ])
            .should_reject(["fora", "exis", "ex ists", "forall1", "exists("]);
    }

    #[test]
    fn parse_variable() {
        VariableParser
            .should_parse_into([
                (
                    "X",
                    Variable {
                        name: "X".into(),
                        sort: Sort::General,
                    },
                ),
                (
                    "G1",
                    Variable {
                        name: "G1".into(),
                        sort: Sort::General,
                    },
                ),
                (
                    "X$i",
                    Variable {
                        name: "X".into(),
                        sort: Sort::Integer,
                    },
                ),
                (
                    "X$",
                    Variable {
                        name: "X".into(),
                        sort: Sort::Integer,
                    },
                ),
                (
                    "Y$g",
                    Variable {
                        name: "Y".into(),
                        sort: Sort::General,
                    },
                ),
            ])
            .should_reject(["X$k", "X $i", "$i", "$g", "a$g"]);
    }

    #[test]
    fn parse_quantification() {
        QuantificationParser
            .should_parse_into([
                (
                    "exists X",
                    Quantification {
                        quantifier: Quantifier::Exists,
                        variables: vec![Variable {
                            name: "X".into(),
                            sort: Sort::General,
                        }],
                    },
                ),
                (
                    "forall X$i Y Z$g",
                    Quantification {
                        quantifier: Quantifier::Forall,
                        variables: vec![
                            Variable {
                                name: "X".into(),
                                sort: Sort::Integer,
                            },
                            Variable {
                                name: "Y".into(),
                                sort: Sort::General,
                            },
                            Variable {
                                name: "Z".into(),
                                sort: Sort::General,
                            },
                        ],
                    },
                ),
                (
                    "exists G1 G1$i",
                    Quantification {
                        quantifier: Quantifier::Exists,
                        variables: vec![
                            Variable {
                                name: "G1".into(),
                                sort: Sort::General,
                            },
                            Variable {
                                name: "G1".into(),
                                sort: Sort::Integer,
                            },
                        ],
                    },
                ),
            ])
            .should_reject([
                "forall",
                "exists ",
                "exists aA",
                "forall X$k",
                "exists X$i$g",
            ]);
    }

    #[test]
    fn parse_formula() {
        FormulaParser
            .should_parse_into([
                (
                    "order",
                    Formula::AtomicFormula(AtomicFormula::Atom(Atom {
                        predicate_symbol: "order".into(),
                        terms: vec![],
                    })),
                ),
                (
                    "andromeda",
                    Formula::AtomicFormula(AtomicFormula::Atom(Atom {
                        predicate_symbol: "andromeda".into(),
                        terms: vec![],
                    })),
                ),
                (
                    "exists_now",
                    Formula::AtomicFormula(AtomicFormula::Atom(Atom {
                        predicate_symbol: "exists_now".into(),
                        terms: vec![],
                    })),
                ),
                (
                    "not p",
                    Formula::UnaryFormula {
                        connective: UnaryConnective::Negation,
                        formula: Formula::AtomicFormula(AtomicFormula::Atom(Atom {
                            predicate_symbol: "p".into(),
                            terms: vec![],
                        }))
                        .into(),
                    },
                ),
                (
                    "forall A p(A) -> q",
                    Formula::BinaryFormula {
                        connective: BinaryConnective::Implication,
                        lhs: Formula::QuantifiedFormula {
                            quantification: Quantification {
                                quantifier: Quantifier::Forall,
                                variables: vec![Variable {
                                    name: "A".into(),
                                    sort: Sort::General,
                                }],
                            },
                            formula: Formula::AtomicFormula(AtomicFormula::Atom(Atom {
                                predicate_symbol: "p".into(),
                                terms: vec![GeneralTerm::Variable("A".into())],
                            }))
                            .into(),
                        }
                        .into(),
                        rhs: Formula::AtomicFormula(AtomicFormula::Atom(Atom {
                            predicate_symbol: "q".into(),
                            terms: vec![],
                        }))
                        .into(),
                    },
                ),
                (
                    "forall A (p(A)) -> #false",
                    Formula::BinaryFormula {
                        connective: BinaryConnective::Implication,
                        lhs: Formula::QuantifiedFormula {
                            quantification: Quantification {
                                quantifier: Quantifier::Forall,
                                variables: vec![Variable {
                                    name: "A".into(),
                                    sort: Sort::General,
                                }],
                            },
                            formula: Formula::AtomicFormula(AtomicFormula::Atom(Atom {
                                predicate_symbol: "p".into(),
                                terms: vec![GeneralTerm::Variable("A".into())],
                            }))
                            .into(),
                        }
                        .into(),
                        rhs: Formula::AtomicFormula(AtomicFormula::Falsity).into(),
                    },
                ),
                (
                    "forall A (p(A)) -> #true",
                    Formula::BinaryFormula {
                        connective: BinaryConnective::Implication,
                        lhs: Formula::QuantifiedFormula {
                            quantification: Quantification {
                                quantifier: Quantifier::Forall,
                                variables: vec![Variable {
                                    name: "A".into(),
                                    sort: Sort::General,
                                }],
                            },
                            formula: Formula::AtomicFormula(AtomicFormula::Atom(Atom {
                                predicate_symbol: "p".into(),
                                terms: vec![GeneralTerm::Variable("A".into())],
                            }))
                            .into(),
                        }
                        .into(),
                        rhs: Formula::AtomicFormula(AtomicFormula::Truth).into(),
                    },
                ),
                (
                    "#true or #false",
                    Formula::BinaryFormula {
                        connective: BinaryConnective::Disjunction,
                        lhs: Formula::AtomicFormula(AtomicFormula::Truth).into(),
                        rhs: Formula::AtomicFormula(AtomicFormula::Falsity).into(),
                    },
                ),
                (
                    "forall V1 V2 (not not ra(V1, V2) -> ra(V1, V2))",
                    Formula::QuantifiedFormula {
                        quantification: Quantification {
                            quantifier: Quantifier::Forall,
                            variables: vec![
                                Variable {
                                    name: "V1".into(),
                                    sort: Sort::General,
                                },
                                Variable {
                                    name: "V2".into(),
                                    sort: Sort::General,
                                },
                            ],
                        },
                        formula: Formula::BinaryFormula {
                            connective: BinaryConnective::Implication,
                            lhs: Formula::UnaryFormula {
                                connective: UnaryConnective::Negation,
                                formula: Formula::UnaryFormula {
                                    connective: UnaryConnective::Negation,
                                    formula: Formula::AtomicFormula(AtomicFormula::Atom(Atom {
                                        predicate_symbol: "ra".to_string(),
                                        terms: vec![
                                            GeneralTerm::Variable("V1".into()),
                                            GeneralTerm::Variable("V2".into()),
                                        ],
                                    }))
                                    .into(),
                                }
                                .into(),
                            }
                            .into(),
                            rhs: Formula::AtomicFormula(AtomicFormula::Atom(Atom {
                                predicate_symbol: "ra".to_string(),
                                terms: vec![
                                    GeneralTerm::Variable("V1".into()),
                                    GeneralTerm::Variable("V2".into()),
                                ],
                            }))
                            .into(),
                        }
                        .into(),
                    },
                ),
                (
                    "exists X$i G(p(G, X$i+30) <-> q or r and t)",
                    Formula::QuantifiedFormula {
                        quantification: Quantification {
                            quantifier: Quantifier::Exists,
                            variables: vec![
                                Variable {
                                    name: "X".into(),
                                    sort: Sort::Integer,
                                },
                                Variable {
                                    name: "G".into(),
                                    sort: Sort::General,
                                },
                            ],
                        },
                        formula: Formula::BinaryFormula {
                            connective: BinaryConnective::Equivalence,
                            lhs: Formula::AtomicFormula(AtomicFormula::Atom(Atom {
                                predicate_symbol: "p".into(),
                                terms: vec![
                                    GeneralTerm::Variable("G".into()),
                                    GeneralTerm::IntegerTerm(IntegerTerm::BinaryOperation {
                                        op: BinaryOperator::Add,
                                        lhs: IntegerTerm::Variable("X".into()).into(),
                                        rhs: IntegerTerm::Numeral(30).into(),
                                    }),
                                ],
                            }))
                            .into(),
                            rhs: Formula::BinaryFormula {
                                connective: BinaryConnective::Disjunction,
                                lhs: Formula::AtomicFormula(AtomicFormula::Atom(Atom {
                                    predicate_symbol: "q".into(),
                                    terms: vec![],
                                }))
                                .into(),
                                rhs: Formula::BinaryFormula {
                                    connective: BinaryConnective::Conjunction,
                                    lhs: Formula::AtomicFormula(AtomicFormula::Atom(Atom {
                                        predicate_symbol: "r".into(),
                                        terms: vec![],
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
                        }
                        .into(),
                    },
                ),
            ])
            .should_reject([
                "not",
                "or",
                "and",
                "exists",
                "forall",
                "or and or",
                "and or and",
            ]);
    }

    #[test]
    fn parse_theory() {
        TheoryParser.should_parse_into([
            ("", Theory { formulas: vec![] }),
            (
                "a.\n",
                Theory {
                    formulas: vec![Formula::AtomicFormula(AtomicFormula::Atom(Atom {
                        predicate_symbol: "a".into(),
                        terms: vec![],
                    }))],
                },
            ),
            (
                "% First comment. \na. %%%% Second comment %%%%\n%Last comment",
                Theory {
                    formulas: vec![Formula::AtomicFormula(AtomicFormula::Atom(Atom {
                        predicate_symbol: "a".into(),
                        terms: vec![],
                    }))],
                },
            ),
            (
                "% comment \nnot a.",
                Theory {
                    formulas: vec![Formula::UnaryFormula {
                        connective: UnaryConnective::Negation,
                        formula: Formula::AtomicFormula(AtomicFormula::Atom(Atom {
                            predicate_symbol: "a".into(),
                            terms: vec![],
                        }))
                        .into(),
                    }],
                },
            ),
            (
                "\nforall X (#false).",
                Theory {
                    formulas: vec![Formula::QuantifiedFormula {
                        quantification: Quantification {
                            quantifier: Quantifier::Forall,
                            variables: vec![Variable {
                                name: "X".into(),
                                sort: Sort::General,
                            }],
                        },
                        formula: Formula::AtomicFormula(AtomicFormula::Falsity).into(),
                    }],
                },
            ),
        ]);
    }

    #[test]
    fn parse_role() {
        RoleParser
            .should_parse_into([
                ("assumption", Role::Assumption),
                ("spec", Role::Spec),
                ("lemma", Role::Lemma),
                ("definition", Role::Definition),
                ("inductive-lemma", Role::InductiveLemma),
            ])
            .should_reject([
                "assume",
                "specification",
                "inductive_lemma",
                "inductive lemma",
                "def",
            ]);
    }

    #[test]
    fn parse_direction() {
        DirectionParser
            .should_parse_into([
                ("universal", Direction::Universal),
                ("forward", Direction::Forward),
                ("backward", Direction::Backward),
            ])
            .should_reject(["backwards", "forwards"]);
    }

    #[test]
    fn parse_annotated_formula() {
        AnnotatedFormulaParser
            .should_parse_into([
                (
                    "lemma: 2 > 1",
                    AnnotatedFormula {
                        role: Role::Lemma,
                        direction: Direction::Universal,
                        name: String::default(),
                        formula: Formula::AtomicFormula(AtomicFormula::Comparison(Comparison {
                            term: GeneralTerm::IntegerTerm(IntegerTerm::Numeral(2)),
                            guards: vec![Guard {
                                relation: Relation::Greater,
                                term: GeneralTerm::IntegerTerm(IntegerTerm::Numeral(1)),
                            }],
                        })),
                    },
                ),
                (
                    "spec(forward)[about_p_0]: not p(0)",
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
                ),
                (
                    "assumption: p(5)",
                    AnnotatedFormula {
                        role: Role::Assumption,
                        direction: Direction::Universal,
                        name: String::default(),
                        formula: Formula::AtomicFormula(AtomicFormula::Atom(Atom {
                            predicate_symbol: "p".into(),
                            terms: vec![GeneralTerm::IntegerTerm(IntegerTerm::Numeral(5))],
                        })),
                    },
                ),
                (
                    "lemma(forward): a > 1",
                    AnnotatedFormula {
                        role: Role::Lemma,
                        direction: Direction::Forward,
                        name: String::default(),
                        formula: Formula::AtomicFormula(AtomicFormula::Comparison(Comparison {
                            term: GeneralTerm::SymbolicTerm(SymbolicTerm::Symbol("a".to_string())),
                            guards: vec![Guard {
                                relation: Relation::Greater,
                                term: GeneralTerm::IntegerTerm(IntegerTerm::Numeral(1)),
                            }],
                        })),
                    },
                ),
                (
                    "lemma(backward)[false]: #false",
                    AnnotatedFormula {
                        role: Role::Lemma,
                        name: "false".to_string(),
                        direction: Direction::Backward,
                        formula: Formula::AtomicFormula(AtomicFormula::Falsity),
                    },
                ),
                (
                    "definition[comp_1]: forall X (composite(X) <-> q(X))",
                    AnnotatedFormula {
                        role: Role::Definition,
                        name: "comp_1".to_string(),
                        direction: Direction::Universal,
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
                                    predicate_symbol: "composite".into(),
                                    terms: vec![GeneralTerm::Variable("X".into())],
                                }))
                                .into(),
                                rhs: Formula::AtomicFormula(AtomicFormula::Atom(Atom {
                                    predicate_symbol: "q".into(),
                                    terms: vec![GeneralTerm::Variable("X".into())],
                                }))
                                .into(),
                            }
                            .into(),
                        },
                    },
                ),
            ])
            .should_reject(["lemma: X"]);
    }

    #[test]
    fn parse_user_guide_entry() {
        UserGuideEntryParser
            .should_parse_into([
                (
                    "input: n -> integer",
                    UserGuideEntry::PlaceholderDeclaration(PlaceholderDeclaration {
                        name: "n".to_string(),
                        sort: Sort::Integer,
                    }),
                ),
                (
                    "input: a/0",
                    UserGuideEntry::InputPredicate(Predicate {
                        symbol: "a".to_string(),
                        arity: 0,
                    }),
                ),
                (
                    "output: a/1",
                    UserGuideEntry::OutputPredicate(Predicate {
                        symbol: "a".to_string(),
                        arity: 1,
                    }),
                ),
                (
                    "spec: #true",
                    UserGuideEntry::AnnotatedFormula(AnnotatedFormula {
                        role: Role::Spec,
                        direction: Direction::Universal,
                        name: String::default(),
                        formula: Formula::AtomicFormula(AtomicFormula::Truth),
                    }),
                ),
            ])
            .should_reject(["output: p", "input: p(X)", "#false"]);
    }

    #[test]
    fn parse_user_guide() {
        UserGuideParser
            .should_parse_into([
                ("", UserGuide { entries: vec![] }),
                (
                    "input: n -> integer.\nassumption: p(5).",
                    UserGuide {
                        entries: vec![
                            UserGuideEntry::PlaceholderDeclaration(PlaceholderDeclaration {
                                name: "n".to_string(),
                                sort: Sort::Integer,
                            }),
                            UserGuideEntry::AnnotatedFormula(AnnotatedFormula {
                                role: Role::Assumption,
                                direction: Direction::Universal,
                                name: String::default(),
                                formula: Formula::AtomicFormula(AtomicFormula::Atom(Atom {
                                    predicate_symbol: "p".into(),
                                    terms: vec![GeneralTerm::IntegerTerm(IntegerTerm::Numeral(5))],
                                })),
                            }),
                        ],
                    },
                ),
                (
                    "% comment \ninput: n -> integer.",
                    UserGuide {
                        entries: vec![UserGuideEntry::PlaceholderDeclaration(
                            PlaceholderDeclaration {
                                name: "n".to_string(),
                                sort: Sort::Integer,
                            },
                        )],
                    },
                ),
                (
                    "\nassumption: p(5).",
                    UserGuide {
                        entries: vec![UserGuideEntry::AnnotatedFormula(AnnotatedFormula {
                            role: Role::Assumption,
                            direction: Direction::Universal,
                            name: String::default(),
                            formula: Formula::AtomicFormula(AtomicFormula::Atom(Atom {
                                predicate_symbol: "p".into(),
                                terms: vec![GeneralTerm::IntegerTerm(IntegerTerm::Numeral(5))],
                            })),
                        })],
                    },
                ),
            ])
            .should_reject(["conjecture: p(5)."]);
    }

    #[test]
    fn parse_specification() {
        SpecificationParser
            .should_parse_into([
                ("", Specification { formulas: vec![] }),
                (
                    "spec(forward)[about_p_0]: not p(0).\nassumption: p(5).\ninductive-lemma: forall N$ (N$ >= 0 -> p(N$)).",
                    Specification {
                        formulas: vec![
                            AnnotatedFormula {
                                role: Role::Spec,
                                direction: Direction::Forward,
                                name: "about_p_0".to_string(),
                                formula: Formula::UnaryFormula {
                                    connective: UnaryConnective::Negation,
                                    formula: Formula::AtomicFormula(AtomicFormula::Atom(Atom {
                                        predicate_symbol: "p".into(),
                                        terms: vec![GeneralTerm::IntegerTerm(
                                            IntegerTerm::Numeral(0),
                                        )],
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
                                direction: Direction::Universal,
                                name: String::default(),
                                formula: Formula::QuantifiedFormula {
                                    quantification: Quantification { quantifier: Quantifier::Forall, variables: vec![Variable {name: "N".to_string(), sort: Sort::Integer}] },
                                    formula: Formula::BinaryFormula {
                                        connective: BinaryConnective::Implication,
                                        lhs: Formula::AtomicFormula(AtomicFormula::Comparison(Comparison { term: GeneralTerm::IntegerTerm(IntegerTerm::Variable("N".to_string())), guards: vec![Guard { relation: Relation::GreaterEqual, term: GeneralTerm::IntegerTerm(IntegerTerm::Numeral(0)) }] })).into(),
                                        rhs: Formula::AtomicFormula(AtomicFormula::Atom(Atom {
                                            predicate_symbol: "p".into(),
                                            terms: vec![GeneralTerm::IntegerTerm(IntegerTerm::Variable("N".to_string()))],
                                        })).into(),
                                    }.into()
                                },
                            },
                        ],
                    },
                ),
                (
                    "% comment \nspec: not #false.",
                    Specification {
                        formulas: vec![
                            AnnotatedFormula {
                                role: Role::Spec,
                                direction: Direction::Universal,
                                name: String::default(),
                                formula: Formula::UnaryFormula {
                                    connective: UnaryConnective::Negation,
                                    formula: Formula::AtomicFormula(AtomicFormula::Falsity).into(),
                                }
                            },
                        ],
                    },
                ),
                (
                    "\nassumption: #false.",
                    Specification {
                        formulas: vec![
                            AnnotatedFormula {
                                role: Role::Assumption,
                                direction: Direction::Universal,
                                name: String::default(),
                                formula: Formula::AtomicFormula(AtomicFormula::Falsity),
                            },
                        ],
                    },
                ),
            ])
            .should_reject(["spec(forward)p_0: not p(0)."]);
    }
}
