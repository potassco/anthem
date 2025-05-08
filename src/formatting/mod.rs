use std::fmt::{self, Display, Formatter};

pub mod asp;
pub mod fol;
pub mod superasp;

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum Associativity {
    Left,
    Right,
}

pub trait Precedence: Display {
    fn precedence(&self) -> usize;

    fn associativity(&self) -> Associativity;

    fn mandatory_parentheses(&self) -> bool {
        false
    }

    fn fmt_operator(&self, f: &mut Formatter<'_>) -> fmt::Result;

    fn fmt_unary(&self, inner: impl Precedence, f: &mut Formatter<'_>) -> fmt::Result {
        if self.associativity() == Associativity::Left {
            self.fmt_operator(f)?;
        }

        if inner.mandatory_parentheses() || self.precedence() < inner.precedence() {
            write!(f, "({inner})")?;
        } else {
            write!(f, "{inner}")?;
        }

        if self.associativity() == Associativity::Right {
            self.fmt_operator(f)?;
        }

        Ok(())
    }

    fn fmt_binary(
        &self,
        lhs: impl Precedence,
        rhs: impl Precedence,
        f: &mut Formatter<'_>,
    ) -> fmt::Result {
        if lhs.mandatory_parentheses()
            || self.precedence() < lhs.precedence()
            || self.precedence() == lhs.precedence() && lhs.associativity() == Associativity::Right
        {
            write!(f, "({lhs})")?;
        } else {
            write!(f, "{lhs}")?;
        }

        self.fmt_operator(f)?;

        if rhs.mandatory_parentheses()
            || self.precedence() < rhs.precedence()
            || self.precedence() == rhs.precedence() && self.associativity() == Associativity::Left
        {
            write!(f, "({rhs})")
        } else {
            write!(f, "{rhs}")
        }
    }
}
