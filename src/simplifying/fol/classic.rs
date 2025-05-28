use crate::{
    convenience::unbox::{Unbox as _, fol::UnboxedFormula},
    syntax_tree::fol::{self, AtomicFormula, BinaryConnective, Formula, UnaryConnective},
};

pub const CLASSIC: &[fn(Formula) -> Formula] = &[remove_double_negation];
pub const POSTGAMMA: &[fn(Formula) -> Formula] = &[remove_double_negation, collapse_worlds];

trait ReplaceHereWithThere {
    fn replace_here_with_there(self) -> Self;
}

impl ReplaceHereWithThere for AtomicFormula {
    fn replace_here_with_there(self) -> Self {
        match self {
            AtomicFormula::Atom(fol::Atom {
                predicate_symbol,
                terms,
            }) => AtomicFormula::Atom(fol::Atom {
                predicate_symbol: predicate_symbol.replacen("h", "t", 1),
                terms,
            }),
            x => x,
        }
    }
}

impl ReplaceHereWithThere for Formula {
    fn replace_here_with_there(self) -> Self {
        match self.unbox() {
            UnboxedFormula::AtomicFormula(atomic_formula) => {
                Formula::AtomicFormula(atomic_formula.replace_here_with_there())
            }
            UnboxedFormula::UnaryFormula {
                connective,
                formula,
            } => Formula::UnaryFormula {
                connective,
                formula: formula.replace_here_with_there().into(),
            },
            UnboxedFormula::BinaryFormula {
                connective,
                lhs,
                rhs,
            } => Formula::BinaryFormula {
                connective,
                lhs: lhs.replace_here_with_there().into(),
                rhs: rhs.replace_here_with_there().into(),
            },
            UnboxedFormula::QuantifiedFormula {
                quantification,
                formula,
            } => Formula::QuantifiedFormula {
                quantification,
                formula: formula.replace_here_with_there().into(),
            },
        }
    }
}

pub fn collapse_worlds(formula: Formula) -> Formula {
    // hp(t) and tp(t) => hp(t)
    match formula.unbox() {
        UnboxedFormula::BinaryFormula {
            connective: BinaryConnective::Conjunction,
            lhs,
            rhs,
        } => {
            let new_lhs = lhs.clone().replace_here_with_there();
            if rhs == new_lhs {
                lhs
            } else {
                UnboxedFormula::BinaryFormula {
                    connective: BinaryConnective::Conjunction,
                    lhs,
                    rhs,
                }
                .rebox()
            }
        }

        x => x.rebox(),
    }
}

pub fn remove_double_negation(formula: Formula) -> Formula {
    // Remove double negation
    // e.g. not not F => F

    match formula.unbox() {
        UnboxedFormula::UnaryFormula {
            connective: UnaryConnective::Negation,
            formula:
                Formula::UnaryFormula {
                    connective: UnaryConnective::Negation,
                    formula: inner,
                },
        } => *inner,

        x => x.rebox(),
    }
}

#[cfg(test)]
mod tests {
    use {
        super::{collapse_worlds, remove_double_negation},
        crate::{convenience::apply::Apply as _, syntax_tree::fol::Formula},
    };

    #[test]
    fn test_eliminate_double_negation() {
        assert_eq!(
            "not not a"
                .parse::<Formula>()
                .unwrap()
                .apply(&mut remove_double_negation),
            "a".parse().unwrap()
        )
    }

    #[test]
    fn test_collapse_worlds() {
        for (src, target) in [
            ("hp(X) and tp(X)", "hp(X)"),
            ("hp(X) -> tp(X)", "hp(X) -> tp(X)"),
            (
                "(V1 = Y and (hat_most_f1(Y) and hat_least_f1(Y)) -> hq(V1)) and (V1 = Y and (tat_most_f1(Y) and tat_least_f1(Y)) -> tq(V1))",
                "(V1 = Y and (hat_most_f1(Y) and hat_least_f1(Y)) -> hq(V1))",
            ),
        ] {
            let src: Formula = collapse_worlds(src.parse().unwrap());
            let target: Formula = target.parse().unwrap();

            assert_eq!(src, target, "{src} != {target}");
        }
    }
}
