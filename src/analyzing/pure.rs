use crate::syntax_tree::asp::{BodyLiteral, Program, Rule};

pub trait Purity {
    fn is_pure(&self) -> bool;
}

impl Purity for Program {
    fn is_pure(&self) -> bool {
        let mut pure = true;
        for rule in &self.rules {
            if !rule.is_pure() {
                pure = false;
            }
        }
        pure
    }
}

impl Purity for Rule {
    fn is_pure(&self) -> bool {
        let mut pure = true;
        let globals = &self.global_variables();
        for literal in &self.body.literals {
            match literal {
                BodyLiteral::AtomicFormula(_) => (),
                BodyLiteral::AggregateAtom(atom) => {
                    if !atom.is_valid_counting_atom() || !atom.all_local(globals) {
                        pure = false;
                    }
                }
            }
        }
        pure
    }
}

#[cfg(test)]
mod tests {
    use {super::Purity, crate::syntax_tree::asp::Program, std::str::FromStr};

    #[test]
    fn test_purity() {
        for program in ["p(X) :- q(X)."] {
            assert!(Program::from_str(program).unwrap().is_pure())
        }

        for program in ["p(X) :- q(X), #count{ X, Y : q(X) } <= 5."] {
            assert!(!Program::from_str(program).unwrap().is_pure())
        }
    }
}
