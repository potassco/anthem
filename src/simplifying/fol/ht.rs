use {
    crate::{
        convenience::unbox::{Unbox as _, fol::UnboxedFormula},
        syntax_tree::fol::{
            self, Atom, AtomicFormula, BinaryConnective, Comparison, Formula, GeneralTerm, Guard,
            IntegerTerm, Quantification, Quantifier, Sort, Theory,
        },
        translating::tau_star::choose_fresh_variable_names,
    },
    indexmap::IndexSet,
    lazy_static::lazy_static,
    regex::Regex,
};

lazy_static! {
    static ref ATLEAST: Regex = Regex::new(r"at_least_(?<name>f([0-9]*))").unwrap();
    static ref ATMOST: Regex = Regex::new(r"at_most_(?<name>f([0-9]*))").unwrap();
    static ref EXACTLY: Regex = Regex::new(r"exactly_(?<name>f([0-9]*))").unwrap();
}

pub const HT: &[fn(Formula) -> Formula] = &[exactly];

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

// Need to add axiom schemas relating exactly to atmost and atleast
// if you are going to apply the 'exactly' simplification
pub fn exactly_axioms(theory: Theory) -> Theory {
    let mut axioms = IndexSet::new();
    for p in theory.predicates() {
        if let Some(caps) = EXACTLY.captures(&p.symbol) {
            let var_names = choose_fresh_variable_names(&IndexSet::new(), "V", p.arity);
            let variables: Vec<fol::Variable> = var_names
                .iter()
                .map(|s| fol::Variable {
                    name: s.clone(),
                    sort: Sort::General,
                })
                .collect();
            let terms: Vec<GeneralTerm> = variables.iter().map(|v| v.clone().into()).collect();

            let f = caps["name"].to_string();

            let at_least = Formula::AtomicFormula(AtomicFormula::Atom(Atom {
                predicate_symbol: format!("at_least_{f}"),
                terms: terms.clone(),
            }));

            let at_most = Formula::AtomicFormula(AtomicFormula::Atom(Atom {
                predicate_symbol: format!("at_most_{f}"),
                terms: terms.clone(),
            }));

            // forall X ( exactly_f(X) <-> at_least_f(X) and at_most_f(X))
            let definition = Formula::QuantifiedFormula {
                quantification: Quantification {
                    quantifier: Quantifier::Forall,
                    variables: variables.clone(),
                },
                formula: Formula::BinaryFormula {
                    connective: BinaryConnective::Equivalence,
                    lhs: Formula::AtomicFormula(AtomicFormula::Atom(Atom {
                        predicate_symbol: p.symbol.clone(),
                        terms,
                    }))
                    .into(),
                    rhs: Formula::BinaryFormula {
                        connective: BinaryConnective::Conjunction,
                        lhs: at_least.into(),
                        rhs: at_most.into(),
                    }
                    .into(),
                }
                .into(),
            };

            let y = variables.last().unwrap().clone();

            // forall X Y (exactly_f(X,Y) -> exists N (Y = N & N >= 0))
            let exactly_y_implies_n = Formula::QuantifiedFormula {
                quantification: Quantification {
                    quantifier: Quantifier::Forall,
                    variables: variables.clone(),
                },
                formula: Formula::QuantifiedFormula {
                    quantification: Quantification {
                        quantifier: Quantifier::Exists,
                        variables: vec![fol::Variable {
                            name: "N".into(),
                            sort: Sort::Integer,
                        }],
                    },
                    formula: Formula::BinaryFormula {
                        connective: BinaryConnective::Conjunction,
                        lhs: Formula::AtomicFormula(AtomicFormula::Comparison(Comparison {
                            term: GeneralTerm::Variable(y.name),
                            guards: vec![Guard {
                                relation: fol::Relation::Equal,
                                term: GeneralTerm::IntegerTerm(IntegerTerm::Variable("N".into())),
                            }],
                        }))
                        .into(),
                        rhs: Formula::AtomicFormula(AtomicFormula::Comparison(Comparison {
                            term: GeneralTerm::IntegerTerm(IntegerTerm::Variable("N".into())),
                            guards: vec![Guard {
                                relation: fol::Relation::Equal,
                                term: GeneralTerm::IntegerTerm(IntegerTerm::Numeral(0)),
                            }],
                        }))
                        .into(),
                    }
                    .into(),
                }
                .into(),
            };

            let mut variables = variables;
            variables.pop();
            variables.push(fol::Variable {
                name: "N".to_string(),
                sort: Sort::Integer,
            });

            let terms: Vec<GeneralTerm> = variables.iter().map(|v| v.clone().into()).collect();

            let mut terms_plus_one = terms.clone();
            terms_plus_one[terms.len() - 1] =
                GeneralTerm::IntegerTerm(IntegerTerm::BinaryOperation {
                    op: fol::BinaryOperator::Add,
                    lhs: IntegerTerm::Variable("N".into()).into(),
                    rhs: IntegerTerm::Numeral(1).into(),
                });

            // forall X N (exactly_f(X,N) <-> at_least_f(X,N) & not at_least_f(X,N+1))
            let not_at_least_plus_one = Formula::QuantifiedFormula {
                quantification: Quantification {
                    quantifier: Quantifier::Forall,
                    variables,
                },
                formula: Formula::BinaryFormula {
                    connective: BinaryConnective::Equivalence,
                    lhs: Formula::AtomicFormula(AtomicFormula::Atom(Atom {
                        predicate_symbol: p.symbol,
                        terms: terms.clone(),
                    }))
                    .into(),
                    rhs: Formula::BinaryFormula {
                        connective: BinaryConnective::Conjunction,
                        lhs: Formula::AtomicFormula(AtomicFormula::Atom(Atom {
                            predicate_symbol: format!("at_least_{f}"),
                            terms,
                        }))
                        .into(),
                        rhs: Formula::UnaryFormula {
                            connective: fol::UnaryConnective::Negation,
                            formula: Formula::AtomicFormula(AtomicFormula::Atom(Atom {
                                predicate_symbol: format!("at_least_{f}"),
                                terms: terms_plus_one,
                            }))
                            .into(),
                        }
                        .into(),
                    }
                    .into(),
                }
                .into(),
            };

            axioms.insert(definition);
            axioms.insert(exactly_y_implies_n);
            axioms.insert(not_at_least_plus_one);
        }
    }

    let formulas = Vec::from_iter(axioms);

    Theory { formulas }
}

#[cfg(test)]
mod tests {
    use {
        super::{exactly, exactly_axioms},
        crate::syntax_tree::fol::{Formula, Theory},
    };

    #[test]
    fn test_exactly() {
        for (src, target) in [
            ("at_least_f25(X,5) and at_most_f25(X,5)", "exactly_f25(X,5)"),
            (
                "at_most_f1(X,t,5) and at_least_f1(X,t,5)",
                "exactly_f1(X,t,5)",
            ),
        ] {
            let left = exactly(src.parse().unwrap());
            let right: Formula = target.parse().unwrap();

            assert_eq!(left, right, "{left} \n!=\n {right}");
        }
    }

    #[test]
    fn test_exactly_axioms() {
        for (src, target) in [(
            "forall X ( q or exactly_f1(X,t,5) ).",
            "forall V V1 V2 (exactly_f1(V,V1,V2) <-> at_least_f1(V,V1,V2) and at_most_f1(V,V1,V2)).",
        )] {
            let left = exactly_axioms(src.parse().unwrap());
            let right: Theory = target.parse().unwrap();

            assert_eq!(left, right, "\n{left} \n!=\n {right}");
        }
    }
}
