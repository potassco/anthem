use crate::{
    syntax_tree::asp::mini_gringo::Program,
    translating::formula_representation::natural::Natural as _,
};

pub trait Regularity {
    fn is_regular(&self) -> bool;
}

impl Regularity for Program {
    fn is_regular(&self) -> bool {
        self.clone().natural().is_some()
    }
}

#[cfg(test)]
mod tests {
    use {super::Regularity, crate::syntax_tree::asp::mini_gringo::Program, std::str::FromStr};

    #[test]
    fn test_regularity() {
        for program in ["a.", "p(1 + 2).", "p(1 - 2).", "p(1 * 2).", "p(X..Y)."] {
            assert!(Program::from_str(program).unwrap().is_regular())
        }

        for program in ["p(1 / 2).", "p(1 \\ 2).", "p(X) :- X = (1..X) + Y."] {
            assert!(!Program::from_str(program).unwrap().is_regular())
        }
    }
}
