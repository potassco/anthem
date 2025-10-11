use {
    crate::{
        syntax_tree::fol::sigma_0,
        translating::classical_reduction::completion::{
            Definitions, atomic_formula_from, components, has_head_mismatches,
        },
    },
    indexmap::IndexSet,
};

pub trait OrderedCompletion {
    type Inputs;

    fn ordered_completion(self, inputs: Self::Inputs) -> Option<Self>
    where
        Self: Sized;
}

impl OrderedCompletion for sigma_0::Theory {
    type Inputs = IndexSet<sigma_0::Predicate>;

    fn ordered_completion(self, inputs: Self::Inputs) -> Option<Self> {
        ordered_completion(self, inputs)
    }
}

pub fn ordered_completion(
    theory: sigma_0::Theory,
    inputs: IndexSet<sigma_0::Predicate>,
) -> Option<sigma_0::Theory> {
    let theory_predicates = theory.predicates();

    let (explicit_definitions, constraints) = components(theory)?;

    let mut explicit_predicates = IndexSet::new();
    for formula in explicit_definitions.keys() {
        if let sigma_0::AtomicFormula::Atom(atom) = formula {
            explicit_predicates.insert(atom.predicate());
        }
    }

    let mut definitions = explicit_definitions;
    for predicate in theory_predicates.difference(&explicit_predicates) {
        definitions.insert(atomic_formula_from(predicate), Vec::new());
    }

    if has_head_mismatches(&definitions) {
        return None;
    }

    let mut final_definitions = Definitions::new();
    for (head, body) in definitions {
        if let sigma_0::AtomicFormula::Atom(atom) = head.clone() {
            if !inputs.contains(&atom.predicate()) {
                final_definitions.insert(head, body);
            }
        }
    }

    // rule translations for each p, i.e.
    // forall X (p(X) <- disjoin(rule bodies of p(X)) )
    // this is just the normal completion but instead of equivalences using <-
    let rule_translations = final_definitions.clone().into_iter().map(|(p, bodies)| {
        let v = p.variables();
        sigma_0::Formula::BinaryFormula {
            connective: sigma_0::BinaryConnective::ReverseImplication,
            lhs: sigma_0::Formula::AtomicFormula(p).into(),
            rhs: sigma_0::Formula::disjoin(bodies.into_iter().map(|f_i| {
                let u_i = f_i.free_variables().difference(&v).cloned().collect();
                f_i.quantify(sigma_0::Quantifier::Exists, u_i)
            }))
            .into(),
        }
        .quantify(sigma_0::Quantifier::Forall, v.into_iter().collect())
    });

    // definition parts for each p, i.e.
    // forall X (disjoin(rule bodies of p(X) with order constraint) -> p(X))
    // this is the -> part of normal completion modified to include the order constraints
    let definitions_with_order = final_definitions.into_iter().map(|(p, bodies)| {
        let v = p.variables();
        match p {
            sigma_0::AtomicFormula::Atom(ref head_atom) => sigma_0::Formula::BinaryFormula {
                connective: sigma_0::BinaryConnective::Implication,
                rhs: sigma_0::Formula::disjoin(bodies.into_iter().map(|f_i| {
                    let u_i = f_i.free_variables().difference(&v).cloned().collect();
                    let f_i_with_order = conjoin_order_atoms(f_i, head_atom.clone());
                    f_i_with_order.quantify(sigma_0::Quantifier::Exists, u_i)
                }))
                .into(),
                lhs: sigma_0::Formula::AtomicFormula(p).into(),
            }
            .quantify(sigma_0::Quantifier::Forall, v.into_iter().collect()),
            _ => unreachable!("definitions should only contain atoms as first component"),
        }
    });

    let mut formulas: Vec<_> = constraints
        .into_iter()
        .map(sigma_0::Formula::universal_closure)
        .collect();
    formulas.extend(rule_translations);
    formulas.extend(definitions_with_order);

    Some(sigma_0::Theory { formulas })
}

fn create_order_formula(p: sigma_0::Atom, q: sigma_0::Atom) -> sigma_0::Formula {
    // creates the atomic formula less_p_q(xs, ys)
    // where p(xs) and q(ys) are the given atoms
    sigma_0::Formula::AtomicFormula(sigma_0::AtomicFormula::Atom(sigma_0::Atom {
        predicate_symbol: format!("less_{}_{}", p.predicate_symbol, q.predicate_symbol),
        terms: p.terms.into_iter().chain(q.terms).collect(),
    }))
}

fn conjoin_order_atoms(formula: sigma_0::Formula, head_atom: sigma_0::Atom) -> sigma_0::Formula {
    // replaces all positive atoms q(zs) in formula
    // (i.e. all q(zs) not in the scope of any negation) by
    //   q(zs) and less_q_p(zs, xs)
    // where p(xs) is head_atom
    match formula {
        sigma_0::Formula::AtomicFormula(sigma_0::AtomicFormula::Atom(ref q)) => {
            sigma_0::Formula::BinaryFormula {
                connective: sigma_0::BinaryConnective::Conjunction,
                rhs: create_order_formula(q.clone(), head_atom).into(),
                lhs: formula.into(),
            }
        }
        sigma_0::Formula::AtomicFormula(_) => formula,
        sigma_0::Formula::UnaryFormula {
            connective: sigma_0::UnaryConnective::Negation,
            ..
        } => formula,
        sigma_0::Formula::BinaryFormula {
            connective,
            lhs,
            rhs,
        } => sigma_0::Formula::BinaryFormula {
            connective,
            lhs: conjoin_order_atoms(*lhs, head_atom.clone()).into(),
            rhs: conjoin_order_atoms(*rhs, head_atom).into(),
        },
        sigma_0::Formula::QuantifiedFormula {
            quantification,
            formula,
        } => sigma_0::Formula::QuantifiedFormula {
            quantification,
            formula: conjoin_order_atoms(*formula, head_atom).into(),
        },
    }
}

pub fn ordered_completion_axioms(theory: sigma_0::Theory) -> sigma_0::Theory {
    fn get_general_variables(l: usize, u: usize) -> Vec<sigma_0::GeneralTerm> {
        // l and u are lower and upper bound for index of general variables
        // i.e. return general variables Xl, ..., Xu
        (l..=u)
            .map(|i| sigma_0::GeneralTerm::Variable(format!("X{i}")))
            .collect()
    }

    fn irreflexivity_axiom(p: sigma_0::Predicate) -> sigma_0::Formula {
        // turn predicate p into atom p(xs)
        let p_atom = sigma_0::Atom {
            predicate_symbol: p.symbol,
            terms: get_general_variables(1, p.arity),
        };

        // not less_p_p(xs, xs)
        let formula = sigma_0::Formula::UnaryFormula {
            connective: sigma_0::UnaryConnective::Negation,
            formula: create_order_formula(p_atom.clone(), p_atom).into(),
        };
        let variables = formula.free_variables().into_iter().collect();

        formula.quantify(sigma_0::Quantifier::Forall, variables)
    }

    fn transitivity_axiom(
        p: sigma_0::Predicate,
        q: sigma_0::Predicate,
        r: sigma_0::Predicate,
    ) -> sigma_0::Formula {
        // turn p, q, r into atoms
        // variables of the three atoms need to distinct
        // to do so the variable index goes from 1 to p.arity + q.arity + r.arity
        let p_atom = sigma_0::Atom {
            predicate_symbol: p.symbol,
            terms: get_general_variables(1, p.arity),
        };
        let q_atom = sigma_0::Atom {
            predicate_symbol: q.symbol,
            terms: get_general_variables(p.arity + 1, p.arity + q.arity),
        };
        let r_atom = sigma_0::Atom {
            predicate_symbol: r.symbol,
            terms: get_general_variables(p.arity + q.arity + 1, p.arity + q.arity + r.arity),
        };

        // (less_p_q(xs, ys) and less_q_r(ys, zs)) -> less_p_r(xs, zs)
        let formula = sigma_0::Formula::BinaryFormula {
            connective: sigma_0::BinaryConnective::Implication,
            lhs: Box::new(sigma_0::Formula::BinaryFormula {
                connective: sigma_0::BinaryConnective::Conjunction,
                lhs: create_order_formula(p_atom.clone(), q_atom.clone()).into(),
                rhs: create_order_formula(q_atom, r_atom.clone()).into(),
            }),
            rhs: create_order_formula(p_atom, r_atom).into(),
        };
        let variables = formula.free_variables().into_iter().collect();

        formula.quantify(sigma_0::Quantifier::Forall, variables)
    }

    // reflexivity for each predicate
    let mut axioms: Vec<_> = theory
        .predicates()
        .into_iter()
        .map(irreflexivity_axiom)
        .collect();

    // transitivity for each tuple (p, q, r)
    for p in theory.predicates() {
        for q in theory.predicates() {
            for r in theory.predicates() {
                axioms.push(transitivity_axiom(p.clone(), q.clone(), r))
            }
        }
    }

    sigma_0::Theory { formulas: axioms }
}

#[cfg(test)]
mod tests {
    use super::{OrderedCompletion as _, ordered_completion_axioms};
    use crate::{
        syntax_tree::{asp::mini_gringo, fol::sigma_0},
        translating::formula_representation::tau_star::TauStar as _,
    };
    use indexmap::IndexSet;

    #[test]
    fn test_ordered_completion() {
        for (src, target, inputs) in [
            (
                "p :- q.",
                "p <- q. p -> q and less_q_p.",
                IndexSet::from_iter(vec![sigma_0::Predicate {
                    symbol: "q".to_string(),
                    arity: 0,
                }]),
            ),
            (
                "p(X) :- q.",
                "forall V1 (p(V1) <- exists X (V1 = X and q)). forall V1 (p(V1) -> exists X (V1 = X and (q and less_q_p(V1)))).",
                IndexSet::from_iter(vec![sigma_0::Predicate {
                    symbol: "q".to_string(),
                    arity: 0,
                }]),
            ),
            (
                "p(X) :- q(X).",
                "forall V1 (p(V1) <- exists X (V1 = X and exists Z (Z = X and q(Z)))). forall V1 (p(V1) -> exists X (V1 = X and exists Z (Z = X and (q(Z) and less_q_p(Z, V1))))).",
                IndexSet::from_iter(vec![sigma_0::Predicate {
                    symbol: "q".to_string(),
                    arity: 1,
                }]),
            ),
            (
                "p(X) :- q(X). p(X) :- not r(X).",
                "forall V1 (p(V1) <- exists X (V1 = X and exists Z (Z = X and q(Z))) or exists X (V1 = X and exists Z (Z = X and not r(Z)))). forall V1 (p(V1) -> exists X (V1 = X and exists Z (Z = X and (q(Z) and less_q_p(Z, V1)))) or exists X (V1 = X and exists Z (Z = X and not r(Z)))).",
                IndexSet::from_iter(vec![
                    sigma_0::Predicate {
                        symbol: "q".to_string(),
                        arity: 1,
                    },
                    sigma_0::Predicate {
                        symbol: "r".to_string(),
                        arity: 1,
                    },
                ]),
            ),
            (
                "p(X) :- q(X-1). {p(X)} :- r(X,Y).",
                "forall V1 (p(V1) <- exists X (V1 = X and exists Z (exists I$i J$i (Z = I$i - J$i and I$i = X and J$i = 1) and q(Z))) or exists X Y (V1 = X and exists Z Z1 (Z = X and Z1 = Y and r(Z, Z1)) and not not p(V1))). forall V1 (p(V1) -> exists X (V1 = X and exists Z (exists I$i J$i (Z = I$i - J$i and I$i = X and J$i = 1) and (q(Z) and less_q_p(Z, V1)))) or exists X Y (V1 = X and exists Z Z1 (Z = X and Z1 = Y and (r(Z, Z1) and less_r_p(Z, Z1, V1))) and not not p(V1))).",
                IndexSet::from_iter(vec![
                    sigma_0::Predicate {
                        symbol: "q".to_string(),
                        arity: 1,
                    },
                    sigma_0::Predicate {
                        symbol: "r".to_string(),
                        arity: 2,
                    },
                ]),
            ),
            (
                "t(X,Y) :- e(X,Y). t(X,Z) :- e(X,Y), t(Y,Z).",
                "forall V1 V2 (t(V1, V2) <- exists X Y (V1 = X and V2 = Y and exists Z Z1 (Z = X and Z1 = Y and e(Z, Z1))) or exists X Z Y (V1 = X and V2 = Z and (exists Z Z1 (Z = X and Z1 = Y and e(Z, Z1)) and exists Z1 Z2 (Z1 = Y and Z2 = Z and t(Z1, Z2))))). forall V1 V2 (t(V1, V2) -> exists X Y (V1 = X and V2 = Y and exists Z Z1 (Z = X and Z1 = Y and (e(Z, Z1) and less_e_t(Z, Z1, V1, V2)))) or exists X Z Y (V1 = X and V2 = Z and (exists Z Z1 (Z = X and Z1 = Y and (e(Z, Z1) and less_e_t(Z, Z1, V1, V2))) and exists Z1 Z2 (Z1 = Y and Z2 = Z and (t(Z1, Z2) and less_t_t(Z1, Z2, V1, V2)))))).",
                IndexSet::from_iter(vec![sigma_0::Predicate {
                    symbol: "e".to_string(),
                    arity: 2,
                }]),
            ),
        ] {
            let left = src
                .parse::<mini_gringo::Program>()
                .unwrap()
                .tau_star()
                .ordered_completion(inputs)
                .unwrap();
            let right = target.parse().unwrap();

            assert!(
                left == right,
                "assertion `left == right` failed:\n left:\n{left}\n right:\n{right}"
            );
        }
    }

    #[test]
    fn test_ordered_completion_incompletable() {
        for theory in [
            "forall X (p(X, a) <- q(X)).",
            "forall X (p(X, X) <- q(X)).",
            "forall X (p(X) <- q(X,Y)).",
            "forall V1 V2 (p(V1, V2) <- t). forall V1 X (p(V1, X) <- q).",
        ] {
            let theory: sigma_0::Theory = theory.parse().unwrap();
            assert!(
                theory.clone().ordered_completion(IndexSet::new()).is_none(),
                "`{theory}` should not be completable"
            );
        }
    }

    #[test]
    fn test_ordered_completion_axioms() {
        for (src, target) in [
            (
                "p :- p.",
                "not less_p_p. less_p_p and less_p_p -> less_p_p.",
            ),
            (
                "p(X) :- q.",
                "not less_q_q. forall X1 not less_p_p(X1, X1). less_q_q and less_q_q -> less_q_q. forall X1 (less_q_q and less_q_p(X1) -> less_q_p(X1)). forall X1 (less_q_p(X1) and less_p_q(X1) -> less_q_q). forall X1 X2 (less_q_p(X1) and less_p_p(X1, X2) -> less_q_p(X2)). forall X1 (less_p_q(X1) and less_q_q -> less_p_q(X1)). forall X1 X2 (less_p_q(X1) and less_q_p(X2) -> less_p_p(X1, X2)). forall X1 X2 (less_p_p(X1, X2) and less_p_q(X2) -> less_p_q(X1)). forall X1 X2 X3 (less_p_p(X1, X2) and less_p_p(X2, X3) -> less_p_p(X1, X3)).",
            ),
        ] {
            let left =
                ordered_completion_axioms(src.parse::<mini_gringo::Program>().unwrap().tau_star());
            let right = target.parse().unwrap();

            assert!(
                left == right,
                "assertion `left == right` failed:\n left:\n{left}\n right:\n{right}"
            );
        }
    }
}
