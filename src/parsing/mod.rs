use std::{any::type_name, convert::AsRef};

pub mod asp;
pub mod fol;

pub trait Parser {
    type Node: crate::syntax_tree::Node;
    type Error;

    fn parse<S: AsRef<str>>(input: S) -> Result<Self::Node, Self::Error>;
}

pub trait PestParser: Sized {
    type Node: crate::syntax_tree::Node;

    type InternalParser: pest::Parser<Self::Rule>;
    type Rule: pest::RuleType;
    const RULE: Self::Rule;

    fn translate_pair(pair: pest::iterators::Pair<'_, Self::Rule>) -> Self::Node;

    fn translate_pairs(mut pairs: pest::iterators::Pairs<'_, Self::Rule>) -> Self::Node {
        let pair = pairs.next().unwrap_or_else(|| Self::report_missing_pair());
        if let Some(pair) = pairs.next() {
            Self::report_unexpected_pair(pair)
        };
        Self::translate_pair(pair)
    }

    fn report_missing_pair() -> ! {
        panic!("in {}: no pair found", type_name::<Self>())
    }

    fn report_unexpected_pair(pair: pest::iterators::Pair<'_, Self::Rule>) -> ! {
        panic!("in {}: unexpected pair found: {pair}", type_name::<Self>())
    }
}

impl<T: PestParser> Parser for T {
    type Node = <Self as PestParser>::Node;
    type Error = pest::error::Error<<Self as PestParser>::Rule>;

    fn parse<S: AsRef<str>>(input: S) -> Result<<T as Parser>::Node, <T as Parser>::Error> {
        use pest::{
            error::{Error, ErrorVariant},
            Parser as _, Position,
        };

        let pairs = <Self as PestParser>::InternalParser::parse(Self::RULE, input.as_ref())
            .and_then(|pairs| {
                if pairs.as_str() == input.as_ref() {
                    Ok(pairs)
                } else {
                    Err(Error::new_from_pos(
                        ErrorVariant::CustomError {
                            message: String::from("expected EOI"),
                        },
                        Position::new(input.as_ref(), pairs.as_str().len()).unwrap(),
                    ))
                }
            })?;

        Ok(Self::translate_pairs(pairs))
    }
}