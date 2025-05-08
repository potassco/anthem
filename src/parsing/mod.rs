use std::any::type_name;

pub mod asp;
pub mod fol;
pub mod superasp;

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
        use pest::Parser as _;
        let mut pairs = <Self as PestParser>::InternalParser::parse(Self::RULE, input.as_ref())?;
        assert_eq!(
            pairs.as_str(),
            input.as_ref(),
            "parts of the input where not parsed"
        );
        pairs.next_back(); // remove EOI
        Ok(Self::translate_pairs(pairs))
    }
}

pub trait TestedParser: Parser {
    fn should_parse_into<'a>(
        &self,
        examples: impl IntoIterator<Item = (&'a str, <Self as Parser>::Node)>,
    ) -> &Self {
        for (input, expected) in examples {
            match Self::parse(input) {
                Ok(output) => {
                    assert!(
                        output == expected,
                        "assertion failed: {} parses '{input}' into {output:?} instead of {expected:?}",
                        type_name::<Self>()
                    )
                }
                Err(_) => panic!(
                    "assertion failed: {} rejects '{input}'",
                    type_name::<Self>()
                ),
            }
        }
        self
    }

    fn should_accept<'a>(&self, examples: impl IntoIterator<Item = &'a str>) -> &Self {
        for example in examples {
            assert!(
                Self::parse(example).is_ok(),
                "assertion failed: {} rejects '{example}'",
                type_name::<Self>()
            )
        }
        self
    }

    fn should_reject<'a>(&self, examples: impl IntoIterator<Item = &'a str>) -> &Self {
        for example in examples {
            assert!(
                Self::parse(example).is_err(),
                "assertion failed: {} accepts '{example}'",
                type_name::<Self>()
            )
        }
        self
    }
}

impl<T: Parser> TestedParser for T {}
