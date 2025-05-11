use crate::{
    convenience::unbox::{Unbox as _, fol::UnboxedFormula},
    syntax_tree::fol::{Formula, UnaryConnective},
};

pub const CLASSIC: &[fn(Formula) -> Formula] = &[remove_double_negation];

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
        super::remove_double_negation,
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
}
