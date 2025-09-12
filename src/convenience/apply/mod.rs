use crate::syntax_tree::fol::sigma_0::Formula;

pub trait Apply {
    /// Apply an operation `f` in post-order to each node of a tree
    fn apply(self, f: &mut impl FnMut(Self) -> Self) -> Self
    where
        Self: Sized;

    /// Apply an operation `f` in post-order to each node of a tree until a fixpoint is reached
    fn apply_fixpoint(self, f: &mut impl FnMut(Self) -> Self) -> Self
    where
        Self: Sized + Eq + Clone,
    {
        let mut previous = self;
        let mut current = previous.clone().apply(f);

        while previous != current {
            previous = current;
            current = previous.clone().apply(f);
        }

        current
    }
}

impl Apply for Formula {
    fn apply(self, f: &mut impl FnMut(Self) -> Self) -> Self
    where
        Self: Sized,
    {
        let inner = match self {
            x @ Formula::AtomicFormula(_) => x,

            Formula::UnaryFormula {
                connective,
                formula,
            } => Formula::UnaryFormula {
                connective,
                formula: formula.apply(f).into(),
            },

            Formula::BinaryFormula {
                connective,
                lhs,
                rhs,
            } => Formula::BinaryFormula {
                connective,
                lhs: lhs.apply(f).into(),
                rhs: rhs.apply(f).into(),
            },

            Formula::QuantifiedFormula {
                quantification,
                formula,
            } => Formula::QuantifiedFormula {
                quantification,
                formula: formula.apply(f).into(),
            },
        };
        f(inner)
    }
}
