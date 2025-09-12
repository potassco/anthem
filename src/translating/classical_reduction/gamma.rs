use crate::{
    convenience::apply::Apply as _,
    syntax_tree::fol::sigma_0::{
        AtomicFormula, BinaryConnective, Formula, Theory, UnaryConnective,
    },
};

pub trait Gamma {
    fn gamma(self) -> Self;
}

impl Gamma for Theory {
    fn gamma(self) -> Self {
        self.into_iter().map(Gamma::gamma).collect()
    }
}

impl Gamma for Formula {
    fn gamma(self) -> Self {
        match self {
            x @ Formula::AtomicFormula(_) => x.here(),

            Formula::UnaryFormula {
                connective: connective @ UnaryConnective::Negation,
                formula,
            } => Formula::UnaryFormula {
                connective,
                formula: formula.there().into(),
            },

            Formula::BinaryFormula {
                connective:
                    connective @ BinaryConnective::Conjunction
                    | connective @ BinaryConnective::Disjunction,
                lhs,
                rhs,
            } => Formula::BinaryFormula {
                connective,
                lhs: lhs.gamma().into(),
                rhs: rhs.gamma().into(),
            },

            Formula::BinaryFormula {
                connective:
                    connective @ BinaryConnective::Implication
                    | connective @ BinaryConnective::ReverseImplication
                    | connective @ BinaryConnective::Equivalence,
                lhs,
                rhs,
            } => Formula::BinaryFormula {
                connective: BinaryConnective::Conjunction,
                lhs: Formula::BinaryFormula {
                    connective: connective.clone(),
                    lhs: lhs.clone().gamma().into(),
                    rhs: rhs.clone().gamma().into(),
                }
                .into(),
                rhs: Formula::BinaryFormula {
                    connective,
                    lhs: lhs.there().into(),
                    rhs: rhs.there().into(),
                }
                .into(),
            },

            Formula::QuantifiedFormula {
                quantification,
                formula,
            } => Formula::QuantifiedFormula {
                quantification,
                formula: formula.gamma().into(),
            },
        }
    }
}

pub trait Here {
    fn here(self) -> Self;
}

impl Here for Formula {
    fn here(self) -> Self {
        prepend_predicate(self, "h")
    }
}

pub trait There {
    fn there(self) -> Self;
}

impl There for Formula {
    fn there(self) -> Self {
        prepend_predicate(self, "t")
    }
}

fn prepend_predicate(formula: Formula, prefix: &'static str) -> Formula {
    formula.apply(&mut |formula| match formula {
        Formula::AtomicFormula(AtomicFormula::Atom(mut a)) => {
            a.predicate_symbol.insert_str(0, prefix);
            Formula::AtomicFormula(AtomicFormula::Atom(a))
        }
        x => x,
    })
}

#[cfg(test)]
mod tests {
    use {super::Gamma as _, crate::syntax_tree::fol::sigma_0::Formula};

    #[test]
    fn test_gamma() {
        for (src, target) in [
            ("#true", "#true"),
            ("a", "ha"),
            ("a(a)", "ha(a)"),
            ("X > 1", "X > 1"),
            ("not a", "not ta"),
            ("not X > 1", "not X > 1"),
            ("a and not b", "ha and not tb"),
            ("a or not b", "ha or not tb"),
            ("a -> b", "(ha -> hb) and (ta -> tb)"),
            ("a <- b", "(ha <- hb) and (ta <- tb)"),
            ("a <-> b", "(ha <-> hb) and (ta <-> tb)"),
            ("forall X p(X)", "forall X hp(X)"),
            ("exists X p(X)", "exists X hp(X)"),
        ] {
            let left = src.parse::<Formula>().unwrap().gamma();
            let right = target.parse().unwrap();

            assert!(
                left == right,
                "assertion `left == right` failed:\n left:\n{left}\n right:\n{right}"
            );
        }
    }
}
