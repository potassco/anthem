use crate::{
    convenience::unbox::{fol::UnboxedFormula, Unbox as _},
    syntax_tree::fol::{AtomicFormula, BinaryConnective, Formula},
};

pub fn simplify(formula: Formula) -> Formula {
    simplify_outer(match formula {
        x @ Formula::AtomicFormula(_) => x,

        Formula::UnaryFormula {
            connective,
            formula,
        } => Formula::UnaryFormula {
            connective,
            formula: Box::new(simplify(*formula)),
        },

        Formula::BinaryFormula {
            connective,
            lhs,
            rhs,
        } => Formula::BinaryFormula {
            connective,
            lhs: Box::new(simplify(*lhs)),
            rhs: Box::new(simplify(*rhs)),
        },

        Formula::QuantifiedFormula {
            quantification,
            formula,
        } => Formula::QuantifiedFormula {
            quantification,
            formula: Box::new(simplify(*formula)),
        },
    })
}

pub fn simplify_outer(formula: Formula) -> Formula {
    // TODO: Split simplifications into multiple functions?

    match formula.unbox() {
        // Remove identities
        // e.g. F op E => F

        // F and #true => F
        UnboxedFormula::BinaryFormula {
            connective: BinaryConnective::Conjunction,
            lhs,
            rhs: Formula::AtomicFormula(AtomicFormula::Truth),
        } => lhs,

        // #true and F => F
        UnboxedFormula::BinaryFormula {
            connective: BinaryConnective::Conjunction,
            lhs: Formula::AtomicFormula(AtomicFormula::Truth),
            rhs,
        } => rhs,

        // F or #false => F
        UnboxedFormula::BinaryFormula {
            connective: BinaryConnective::Disjunction,
            lhs,
            rhs: Formula::AtomicFormula(AtomicFormula::Falsity),
        } => lhs,

        // #false or F => F
        UnboxedFormula::BinaryFormula {
            connective: BinaryConnective::Disjunction,
            lhs: Formula::AtomicFormula(AtomicFormula::Falsity),
            rhs,
        } => rhs,

        // Remove annihilations
        // e.g. F op E => E

        // F or #true => #true
        UnboxedFormula::BinaryFormula {
            connective: BinaryConnective::Disjunction,
            lhs: _,
            rhs: rhs @ Formula::AtomicFormula(AtomicFormula::Truth),
        } => rhs,

        // #true or F => #true
        UnboxedFormula::BinaryFormula {
            connective: BinaryConnective::Disjunction,
            lhs: lhs @ Formula::AtomicFormula(AtomicFormula::Truth),
            rhs: _,
        } => lhs,

        // F and #false => false
        UnboxedFormula::BinaryFormula {
            connective: BinaryConnective::Conjunction,
            lhs: _,
            rhs: rhs @ Formula::AtomicFormula(AtomicFormula::Falsity),
        } => rhs,

        // #false and F => #false
        UnboxedFormula::BinaryFormula {
            connective: BinaryConnective::Conjunction,
            lhs: lhs @ Formula::AtomicFormula(AtomicFormula::Falsity),
            rhs: _,
        } => lhs,

        // Remove idempotences
        // e.g. F op F => F

        // F and F => F
        // F or  F => F
        UnboxedFormula::BinaryFormula {
            connective: BinaryConnective::Conjunction | BinaryConnective::Disjunction,
            lhs,
            rhs,
        } if lhs == rhs => lhs,

        x => x.rebox(),
    }
}

#[cfg(test)]
mod tests {
    use super::{simplify, simplify_outer};

    #[test]
    fn test_simplify() {
        for (src, target) in [
            ("#true and a", "a"),
            ("a and #true", "a"),
            ("#false or a", "a"),
            ("a or #false", "a"),
            ("#true or a", "#true"),
            ("a or #true", "#true"),
            ("#false and a", "#false"),
            ("a and #false", "#false"),
            ("a and a", "a"),
            ("a or a", "a"),
            ("#true and #true and a", "a"),
            ("#true and (#true and a)", "a"),
        ] {
            assert_eq!(simplify(src.parse().unwrap()), target.parse().unwrap())
        }
    }

    #[test]
    fn test_simplify_outer() {
        for (src, target) in [
            ("#true and a", "a"),
            ("a and #true", "a"),
            ("#false or a", "a"),
            ("a or #false", "a"),
            ("#true or a", "#true"),
            ("a or #true", "#true"),
            ("#false and a", "#false"),
            ("a and #false", "#false"),
            ("a and a", "a"),
            ("a or a", "a"),
            ("#true and (#true and a)", "#true and a"),
            ("(#true and #true) and a", "(#true and #true) and a"),
        ] {
            assert_eq!(
                simplify_outer(src.parse().unwrap()),
                target.parse().unwrap()
            )
        }
    }
}
