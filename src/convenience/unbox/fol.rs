use crate::syntax_tree::fol::sigma_0::{
    AtomicFormula, BinaryConnective, Formula, Quantification, UnaryConnective,
};

pub enum UnboxedFormula {
    AtomicFormula(AtomicFormula),
    UnaryFormula {
        connective: UnaryConnective,
        formula: Formula,
    },
    BinaryFormula {
        connective: BinaryConnective,
        lhs: Formula,
        rhs: Formula,
    },
    QuantifiedFormula {
        quantification: Quantification,
        formula: Formula,
    },
}

impl UnboxedFormula {
    pub fn rebox(self) -> Formula {
        match self {
            Self::AtomicFormula(f) => Formula::AtomicFormula(f),
            Self::UnaryFormula {
                connective,
                formula,
            } => Formula::UnaryFormula {
                connective,
                formula: Box::new(formula),
            },
            Self::BinaryFormula {
                connective,
                lhs,
                rhs,
            } => Formula::BinaryFormula {
                connective,
                lhs: Box::new(lhs),
                rhs: Box::new(rhs),
            },
            Self::QuantifiedFormula {
                quantification,
                formula,
            } => Formula::QuantifiedFormula {
                quantification,
                formula: Box::new(formula),
            },
        }
    }
}
