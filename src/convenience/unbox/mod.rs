use crate::syntax_tree::fol::sigma_0::Formula;

use self::fol::UnboxedFormula;

pub mod fol;

pub trait Unbox {
    type Unboxed;

    fn unbox(self) -> Self::Unboxed;
}

impl Unbox for Formula {
    type Unboxed = UnboxedFormula;

    fn unbox(self) -> UnboxedFormula {
        match self {
            Self::AtomicFormula(f) => UnboxedFormula::AtomicFormula(f),
            Self::UnaryFormula {
                connective,
                formula,
            } => UnboxedFormula::UnaryFormula {
                connective,
                formula: *formula,
            },
            Self::BinaryFormula {
                connective,
                lhs,
                rhs,
            } => UnboxedFormula::BinaryFormula {
                connective,
                lhs: *lhs,
                rhs: *rhs,
            },
            Self::QuantifiedFormula {
                quantification,
                formula,
            } => UnboxedFormula::QuantifiedFormula {
                quantification,
                formula: *formula,
            },
        }
    }
}
