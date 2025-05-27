use {
    super::counting::TargetTheory,
    crate::{
        convenience::{
            apply::Apply as _,
            compose::Compose as _,
            unbox::{Unbox, fol::UnboxedFormula},
        },
        simplifying::fol::{
            ht::{COUNT, HT, exactly_axioms},
            intuitionistic::INTUITIONISTIC,
        },
        syntax_tree::fol::{self, Theory},
    },
    indexmap::{IndexMap, IndexSet, map::Entry},
    itertools::Itertools,
};

pub(crate) fn completion_with_axioms(theory: TargetTheory) -> Option<TargetTheory> {
    match completion(Theory::from_iter(theory.formulas)) {
        Some(completed_theory) => {
            let mut portfolio = [INTUITIONISTIC, HT, COUNT].concat().into_iter().compose();

            let mut formulas = IndexSet::new();
            let mut axioms = IndexSet::new();

            for formula in completed_theory.formulas {
                formulas.insert(formula.apply_fixpoint(&mut portfolio));
            }
            for formula in theory.axioms {
                axioms.insert(formula);
            }

            let simplified_theory = Theory::from_iter(formulas);
            for formula in exactly_axioms(simplified_theory.clone()) {
                axioms.insert(formula);
            }

            Some(TargetTheory {
                formulas: simplified_theory.formulas,
                axioms: Vec::from_iter(axioms),
            })
        }
        None => None,
    }
}

pub fn completion(theory: fol::Theory) -> Option<fol::Theory> {
    // Retrieve the definitions and constraints
    let (definitions, constraints) = components(theory)?;

    // Confirm there are no head mismatches
    if has_head_mismatches(&definitions) {
        return None;
    }

    // Complete the definitions
    let completed_definitions = definitions.into_iter().map(|(g, a)| {
        let v = g.variables();
        fol::Formula::BinaryFormula {
            connective: fol::BinaryConnective::Equivalence,
            lhs: fol::Formula::AtomicFormula(g).into(),
            rhs: fol::Formula::disjoin(a.into_iter().map(|f_i| {
                let u_i = f_i.free_variables().difference(&v).cloned().collect();
                f_i.quantify(fol::Quantifier::Exists, u_i)
            }))
            .into(),
        }
        .quantify(fol::Quantifier::Forall, v.into_iter().collect())
    });

    let mut formulas: Vec<_> = constraints
        .into_iter()
        .map(fol::Formula::universal_closure)
        .collect();
    formulas.extend(completed_definitions);

    Some(fol::Theory { formulas })
}

pub(crate) fn has_head_mismatches(definitions: &Definitions) -> bool {
    for (_, heads) in heads(definitions) {
        if !heads.iter().all_equal() {
            return true;
        }
    }
    false
}

fn heads(definitions: &Definitions) -> IndexMap<fol::Predicate, Vec<&fol::AtomicFormula>> {
    let mut result: IndexMap<_, Vec<_>> = IndexMap::new();
    for head in definitions.keys() {
        if let fol::AtomicFormula::Atom(a) = head {
            match result.entry(a.predicate()) {
                Entry::Occupied(mut e) => {
                    e.get_mut().push(head);
                }
                Entry::Vacant(e) => {
                    e.insert(vec![head]);
                }
            }
        } else {
            unreachable!();
        }
    }
    result
}

pub(crate) fn components(theory: fol::Theory) -> Option<(Definitions, Constraints)> {
    let mut definitions: Definitions = IndexMap::new();
    let mut constraints = Vec::new();

    for formula in theory.formulas {
        match split(formula)? {
            Component::Constraint(c) => constraints.push(c),
            Component::PartialDefinition { f, a } => match definitions.entry(a) {
                Entry::Occupied(mut e) => {
                    e.get_mut().push(f);
                }
                Entry::Vacant(e) => {
                    e.insert(vec![f]);
                }
            },
        }
    }

    Some((definitions, constraints))
}

type Definitions = IndexMap<fol::AtomicFormula, Vec<fol::Formula>>;
type Constraints = Vec<fol::Formula>;

fn split(formula: fol::Formula) -> Option<Component> {
    if !formula.free_variables().is_empty() {
        return None;
    }

    match formula {
        fol::Formula::QuantifiedFormula {
            quantification:
                fol::Quantification {
                    quantifier: fol::Quantifier::Forall,
                    ..
                },
            formula,
        } => split_implication(*formula),
        formula => split_implication(formula),
    }
}

fn split_implication(formula: fol::Formula) -> Option<Component> {
    match formula.clone().unbox() {
        UnboxedFormula::BinaryFormula {
            connective: fol::BinaryConnective::Implication,
            lhs: f,
            rhs: g,
        }
        | UnboxedFormula::BinaryFormula {
            connective: fol::BinaryConnective::ReverseImplication,
            lhs: g,
            rhs: f,
        } => match g {
            // TODO: What about fol::AtomicFormula::Truth?
            fol::Formula::AtomicFormula(fol::AtomicFormula::Falsity) => {
                Some(Component::Constraint(formula))
            }
            fol::Formula::AtomicFormula(fol::AtomicFormula::Atom(a)) => {
                let mut v = a.terms.iter().map(|t| match t {
                    fol::GeneralTerm::Variable(v) => Some(fol::Variable {
                        name: v.clone(),
                        sort: fol::Sort::General,
                    }),
                    fol::GeneralTerm::IntegerTerm(fol::IntegerTerm::Variable(v)) => {
                        Some(fol::Variable {
                            name: v.clone(),
                            sort: fol::Sort::Integer,
                        })
                    }
                    fol::GeneralTerm::SymbolicTerm(fol::SymbolicTerm::Variable(v)) => {
                        Some(fol::Variable {
                            name: v.clone(),
                            sort: fol::Sort::Symbol,
                        })
                    }
                    _ => None,
                });

                if v.clone().contains(&None) | !v.all_unique() {
                    None
                } else {
                    Some(Component::PartialDefinition {
                        f,
                        a: fol::AtomicFormula::Atom(a),
                    })
                }
            }
            _ => None,
        },
        _ => None,
    }
}

enum Component {
    PartialDefinition {
        f: fol::Formula,
        a: fol::AtomicFormula,
    },
    Constraint(fol::Formula),
}

#[cfg(test)]
mod tests {
    use crate::{
        syntax_tree::fol,
        translating::{completion::completion, tau_star::tau_star},
    };

    #[test]
    fn test_completion() {
        for (src, target) in [
            (
                "p(X) :- q(X).",
                "forall V1 (p(V1) <-> exists X (V1 = X and exists Z (Z = X and q(Z)))).",
            ),
            (
                "p(a). p(b). q(X,Y) :- p(X), p(Y).",
                "forall V1 (p(V1) <-> V1 = a and #true or V1 = b and #true). forall V1 V2 (q(V1, V2) <-> exists X Y (V1 = X and V2 = Y and (exists Z (Z = X and p(Z)) and exists Z (Z = Y and p(Z))))).",
            ),
            (
                "{p(X+1)} :- q(X).",
                "forall V1 (p(V1) <-> exists X (exists I$i J$i (V1 = I$i + J$i and I$i = X and J$i = 1) and exists Z (Z = X and q(Z)) and not not p(V1))).",
            ),
            (
                "r(X) :- q(X). r(G,Y) :- G < Y. r(a).",
                "forall V1 (r(V1) <-> exists X (V1 = X and exists Z (Z = X and q(Z))) or V1 = a and #true). forall V1 V2 (r(V1,V2) <-> exists G Y (V1 = G and V2 = Y and exists Z Z1 (Z = G and Z1 = Y and Z < Z1) ) ).",
            ),
            (
                "composite(I*J) :- I>1, J>1. prime(I) :- I = 2..n, not composite(I).",
                "forall V1 (composite(V1) <-> exists I J (exists I1$i J1$i (V1 = I1$i * J1$i and I1$i = I and J1$i = J) and (exists Z Z1 (Z = I and Z1 = 1 and Z > Z1) and exists Z Z1 (Z = J and Z1 = 1 and Z > Z1)))). forall V1 (prime(V1) <-> exists I (V1 = I and (exists Z Z1 (Z = I and exists I$i J$i K$i (I$i = 2 and J$i = n and Z1 = K$i and I$i <= K$i <= J$i) and Z = Z1) and exists Z (Z = I and not composite(Z))))).",
            ),
            (
                "p :- q, not t. p :- r. r :- t.",
                "p <-> (q and not t) or (r). r <-> t.",
            ),
            (
                "p. p(a). :- q.",
                "q -> #false. p <-> #true. forall V1 (p(V1) <-> V1 = a and #true).",
            ),
            (
                "p(X) :- q(X, Y).",
                "forall V1 (p(V1) <-> exists X Y (V1 = X and exists Z Z1 (Z = X and Z1 = Y and q(Z, Z1)))).",
            ),
            (
                ":- s(X, I), not covered(X).",
                "forall X I (exists Z Z1 (Z = X and Z1 = I and s(Z, Z1)) and exists Z (Z = X and not covered(Z)) -> #false).",
            ),
        ] {
            let left = completion(tau_star(src.parse().unwrap())).unwrap();
            let right = target.parse().unwrap();

            assert!(
                left == right,
                "assertion `left == right` failed:\n left:\n{left}\n right:\n{right}"
            );
        }
    }

    #[test]
    fn test_incompletable() {
        for theory in [
            "forall X (p(X, a) <- q(X)).",
            "forall X (p(X, X) <- q(X)).",
            "forall X (p(X) <- q(X,Y)).",
            "forall V1 V2 (p(V1, V2) <- t). forall V1 X (p(V1,X) <- q).",
        ] {
            let theory: fol::Theory = theory.parse().unwrap();
            assert!(
                completion(theory.clone()).is_none(),
                "`{theory}` should not be completable"
            );
        }
    }
}
