use {
    crate::{
        convenience::unbox::{Unbox as _, fol::UnboxedFormula},
        syntax_tree::fol::{Atom, AtomicFormula, BinaryConnective, Formula, GeneralTerm},
    },
    lazy_static::lazy_static,
    regex::Regex,
};

lazy_static! {
    static ref ATLEAST: Regex = Regex::new(r"at_least_(?<name>f([0-9]*))").unwrap();
    static ref ATMOST: Regex = Regex::new(r"at_most_(?<name>f([0-9]*))").unwrap();
}

pub const HT: &[fn(Formula) -> Formula] = &[];

#[derive(Clone, Debug, Eq, PartialEq)]
struct AtomIdentifier {
    name: String,
    terms: Vec<GeneralTerm>,
    last_term: GeneralTerm,
}

fn at_least_atom(formula: &Formula) -> Option<AtomIdentifier> {
    match formula {
        Formula::AtomicFormula(AtomicFormula::Atom(atom)) => {
            let caps = ATLEAST.captures(&atom.predicate_symbol)?;

            if atom.terms.is_empty() {
                return None;
            }

            let mut terms = atom.terms.clone();
            let last_term = terms.pop().unwrap();

            Some(AtomIdentifier {
                name: caps["name"].to_string(),
                terms,
                last_term,
            })
        }
        _ => None,
    }
}

fn at_most_atom(formula: &Formula) -> Option<AtomIdentifier> {
    match formula {
        Formula::AtomicFormula(AtomicFormula::Atom(atom)) => {
            let caps = ATMOST.captures(&atom.predicate_symbol)?;

            if atom.terms.is_empty() {
                return None;
            }

            let mut terms = atom.terms.clone();
            let last_term = terms.pop().unwrap();

            Some(AtomIdentifier {
                name: caps["name"].to_string(),
                terms,
                last_term,
            })
        }
        _ => None,
    }
}

// TODO - need to add axiom schemas relating exactly to atmost and atleast if you are going to apply this simplification

// Assumes boldt, t are tuples and singleton terms
// also assumes no one wrote a predicate matching the at_least or at_most regex
pub fn exactly(formula: Formula) -> Formula {
    // at_least_f(boldt, t) & at_most_f(boldt, t) => exactly_f(boldt, t)
    // at_most_f(boldt, t) & at_least_f(boldt, t) => exactly_f(boldt, t)
    match formula.clone().unbox() {
        UnboxedFormula::BinaryFormula {
            connective: BinaryConnective::Conjunction,
            lhs,
            rhs,
        } => {
            let lhs_least = at_least_atom(&lhs);
            let rhs_most = at_most_atom(&rhs);

            let rhs_least = at_least_atom(&rhs);
            let lhs_most = at_most_atom(&lhs);

            if lhs_least.is_some() && rhs_most.is_some() {
                match (lhs_least, rhs_most) {
                    (Some(left), Some(right)) if left == right => {
                        let mut terms = left.terms;
                        terms.push(left.last_term);

                        Formula::AtomicFormula(AtomicFormula::Atom(Atom {
                            predicate_symbol: format!("exactly_{}", left.name),
                            terms,
                        }))
                    }
                    _ => formula,
                }
            } else if rhs_least.is_some() && lhs_most.is_some() {
                match (rhs_least, lhs_most) {
                    (Some(left), Some(right)) if left == right => {
                        let mut terms = left.terms;
                        terms.push(left.last_term);

                        Formula::AtomicFormula(AtomicFormula::Atom(Atom {
                            predicate_symbol: format!("exactly_{}", left.name),
                            terms,
                        }))
                    }
                    _ => formula,
                }
            } else {
                formula
            }
        }
        _ => formula,
    }
}


#[cfg(test)]
mod tests {
    use {
        super::exactly,
        crate::syntax_tree::fol::Formula,
    };

    #[test]
    fn test_exactly() {
        for (src, target) in [
            ("at_least_f25(X,5) and at_most_f25(X,5)", "exactly_f25(X,5)"),
            ("at_most_f1(X,t,5) and at_least_f1(X,t,5)", "exactly_f1(X,t,5)"),
        ] {
            let left = exactly(src.parse().unwrap());
            let right: Formula = target.parse().unwrap();

            assert_eq!(left, right, "{left} \n!=\n {right}");
        }
    }
}
