use crate::{syntax_tree::asp::Program, translating::natural::natural};

pub trait Regularity {
    fn is_regular(&self) -> bool;
}

impl Regularity for Program {
    fn is_regular(&self) -> bool {
        natural(self.clone()).is_some()
    }
}
