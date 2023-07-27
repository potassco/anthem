use crate::{parsing::PestParser, syntax_tree::asp::Constant};

mod internal {
    #[derive(pest_derive::Parser)]
    #[grammar = "parsing/asp/grammar.pest"]
    pub struct Parser;
}

pub struct ConstantParser;

impl PestParser for ConstantParser {
    type Node = Constant;

    type InternalParser = internal::Parser;
    type Rule = internal::Rule;
    const RULE: internal::Rule = internal::Rule::constant;

    fn translate_pair(pair: pest::iterators::Pair<'_, Self::Rule>) -> Self::Node {
        match pair.as_rule() {
            internal::Rule::constant => Self::translate_pairs(pair.into_inner()),
            internal::Rule::infimum => Constant::Infimum,
            internal::Rule::integer => Constant::Integer(pair.as_str().parse().unwrap()),
            internal::Rule::symbol => Constant::Symbol(pair.as_str().into()),
            internal::Rule::supremum => Constant::Supremum,
            _ => Self::report_unexpected_pair(pair),
        }
    }
}

// TODO Tobias: Continue implementing pest parsing for ASP here
