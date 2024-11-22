use {
    super::{replacement_helper, simplify_conjunction_tree_with_equality, transitive_equality},
    crate::{
        convenience::{
            apply::Apply as _,
            unbox::{fol::UnboxedFormula, Unbox as _},
        },
        syntax_tree::fol::{
            AtomicFormula, BinaryConnective, Formula, GeneralTerm, IntegerTerm, Quantification,
            Quantifier, Sort, SymbolicTerm, Theory,
        },
    },
};

pub fn simplify(theory: Theory) -> Theory {
    Theory {
        formulas: theory.formulas.into_iter().map(simplify_formula).collect(),
    }
}

pub fn simplify_formula(formula: Formula) -> Formula {
    formula.apply_all(&mut vec![
        Box::new(remove_identities),
        Box::new(remove_annihilations),
        Box::new(remove_idempotences),
        Box::new(join_nested_quantifiers),
        Box::new(extend_quantifier_scope),
        Box::new(restrict_quantifier_domain),
        // cleanup
        Box::new(simplify_variable_lists),
        Box::new(simplify_empty_quantifiers),
        Box::new(simplify_transitive_equality),
        // cleanup
        Box::new(simplify_variable_lists),
        Box::new(simplify_empty_quantifiers),
    ])
}

pub fn remove_identities(formula: Formula) -> Formula {
    // Remove identities
    // e.g. F op E => F

    match formula.unbox() {
        // F and #true => F
        UnboxedFormula::BinaryFormula {
            connective: BinaryConnective::Conjunction,
            lhs,
            rhs: Formula::AtomicFormula(AtomicFormula::Truth),
        } => lhs,

        // #true and F => F
        UnboxedFormula::BinaryFormula {
            connective: BinaryConnective::Conjunction,
            lhs: Formula::AtomicFormula(AtomicFormula::Truth),
            rhs,
        } => rhs,

        // F or #false => F
        UnboxedFormula::BinaryFormula {
            connective: BinaryConnective::Disjunction,
            lhs,
            rhs: Formula::AtomicFormula(AtomicFormula::Falsity),
        } => lhs,

        // #false or F => F
        UnboxedFormula::BinaryFormula {
            connective: BinaryConnective::Disjunction,
            lhs: Formula::AtomicFormula(AtomicFormula::Falsity),
            rhs,
        } => rhs,

        x => x.rebox(),
    }
}

pub fn remove_annihilations(formula: Formula) -> Formula {
    // Remove annihilations
    // e.g. F op E => E

    match formula.unbox() {
        // F or #true => #true
        UnboxedFormula::BinaryFormula {
            connective: BinaryConnective::Disjunction,
            lhs: _,
            rhs: rhs @ Formula::AtomicFormula(AtomicFormula::Truth),
        } => rhs,

        // #true or F => #true
        UnboxedFormula::BinaryFormula {
            connective: BinaryConnective::Disjunction,
            lhs: lhs @ Formula::AtomicFormula(AtomicFormula::Truth),
            rhs: _,
        } => lhs,

        // F and #false => false
        UnboxedFormula::BinaryFormula {
            connective: BinaryConnective::Conjunction,
            lhs: _,
            rhs: rhs @ Formula::AtomicFormula(AtomicFormula::Falsity),
        } => rhs,

        // #false and F => #false
        UnboxedFormula::BinaryFormula {
            connective: BinaryConnective::Conjunction,
            lhs: lhs @ Formula::AtomicFormula(AtomicFormula::Falsity),
            rhs: _,
        } => lhs,

        x => x.rebox(),
    }
}

pub fn remove_idempotences(formula: Formula) -> Formula {
    // Remove idempotences
    // e.g. F op F => F

    match formula.unbox() {
        // F and F => F
        // F or  F => F
        UnboxedFormula::BinaryFormula {
            connective: BinaryConnective::Conjunction | BinaryConnective::Disjunction,
            lhs,
            rhs,
        } if lhs == rhs => lhs,

        x => x.rebox(),
    }
}

pub fn join_nested_quantifiers(formula: Formula) -> Formula {
    // Remove nested quantifiers
    // e.g. q X ( q Y F(X,Y) ) => q X Y F(X,Y)

    match formula.unbox() {
        // forall X ( forall Y F(X,Y) ) => forall X Y F(X,Y)
        // exists X ( exists Y F(X,Y) ) => exists X Y F(X,Y)
        UnboxedFormula::QuantifiedFormula {
            quantification: outer_quantification,
            formula:
                Formula::QuantifiedFormula {
                    quantification: mut inner_quantification,
                    formula: inner_formula,
                },
        } if outer_quantification.quantifier == inner_quantification.quantifier => {
            let mut variables = outer_quantification.variables;
            variables.append(&mut inner_quantification.variables);
            variables.sort();
            variables.dedup();

            inner_formula.quantify(outer_quantification.quantifier, variables)
        }
        x => x.rebox(),
    }
}

pub fn extend_quantifier_scope(formula: Formula) -> Formula {
    match formula.clone().unbox() {
        // Bring a conjunctive or disjunctive term into the scope of a quantifer
        // e.g. exists X ( F(X) ) & G => exists X ( F(X) & G )
        // where X does not occur free in G
        UnboxedFormula::BinaryFormula {
            connective,
            lhs:
                Formula::QuantifiedFormula {
                    quantification:
                        Quantification {
                            quantifier,
                            variables,
                        },
                    formula: f,
                },
            rhs,
        } => match connective {
            BinaryConnective::Conjunction | BinaryConnective::Disjunction => {
                let mut collision = false;
                for var in variables.iter() {
                    if rhs.free_variables().contains(var) {
                        collision = true;
                        break;
                    }
                }

                match collision {
                    true => formula,
                    false => Formula::QuantifiedFormula {
                        quantification: Quantification {
                            quantifier,
                            variables,
                        },
                        formula: Formula::BinaryFormula {
                            connective,
                            lhs: f,
                            rhs: rhs.into(),
                        }
                        .into(),
                    },
                }
            }
            _ => formula,
        },

        UnboxedFormula::BinaryFormula {
            connective,
            lhs,
            rhs:
                Formula::QuantifiedFormula {
                    quantification:
                        Quantification {
                            quantifier,
                            variables,
                        },
                    formula: f,
                },
        } => match connective {
            BinaryConnective::Conjunction | BinaryConnective::Disjunction => {
                let mut collision = false;
                for var in variables.iter() {
                    if lhs.free_variables().contains(var) {
                        collision = true;
                        break;
                    }
                }

                match collision {
                    true => formula,
                    false => Formula::QuantifiedFormula {
                        quantification: Quantification {
                            quantifier,
                            variables,
                        },
                        formula: Formula::BinaryFormula {
                            connective,
                            lhs: lhs.into(),
                            rhs: f,
                        }
                        .into(),
                    },
                }
            }
            _ => formula,
        },

        x => x.rebox(),
    }
}

pub fn simplify_variable_lists(formula: Formula) -> Formula {
    match formula.clone().unbox() {
        // Removes variables from quantifiers when they do not occur in the quantified formula
        // e.g. exists X Y ( q(Y) ) => exists Y ( q(Y) )
        UnboxedFormula::QuantifiedFormula {
            quantification:
                Quantification {
                    mut variables,
                    quantifier,
                },
            formula,
        } => {
            let fvars = formula.variables();
            variables.retain(|x| fvars.contains(x));
            Formula::QuantifiedFormula {
                quantification: Quantification {
                    variables,
                    quantifier,
                },
                formula: formula.into(),
            }
        }

        x => x.rebox(),
    }
}

pub fn simplify_empty_quantifiers(formula: Formula) -> Formula {
    match formula.clone().unbox() {
        // Remove quantifiers with no variables
        // e.g. exists ( F ) => F
        UnboxedFormula::QuantifiedFormula {
            quantification: Quantification { variables, .. },
            formula: f,
        } => {
            if variables.is_empty() {
                f
            } else {
                formula
            }
        }

        x => x.rebox(),
    }
}

pub fn restrict_quantifier_domain(formula: Formula) -> Formula {
    let mut simplified_formula = formula.clone();
    match formula.clone().unbox() {
        // Replace a general variable in an outer quantification with a fresh integer variable capturing an inner quantification
        // e.g. exists Z$g (exists I$i J$i (I$i = Z$g & G) & H) => exists K$i (exists I$i J$i (I$i = K$i & G) & H)
        // or  forall Z$g (exists I$i J$i (I$i = Z$g & G) -> H) => forall K$i (exists I$i J$i (I$i = K$i & G) -> H)
        UnboxedFormula::QuantifiedFormula {
            quantification:
                Quantification {
                    quantifier: Quantifier::Exists,
                    variables: outer_vars,
                },
            formula:
                Formula::BinaryFormula {
                    connective: BinaryConnective::Conjunction,
                    lhs,
                    rhs,
                },
        } => {
            let mut replaced = false;
            let mut conjunctive_terms = Formula::conjoin_invert(*lhs);
            conjunctive_terms.extend(Formula::conjoin_invert(*rhs));
            for ct in conjunctive_terms.iter() {
                if let Formula::QuantifiedFormula {
                    quantification:
                        Quantification {
                            quantifier: Quantifier::Exists,
                            variables: inner_vars,
                        },
                    formula: inner_formula,
                } = ct
                {
                    let inner_ct = Formula::conjoin_invert(*inner_formula.clone());
                    for ict in inner_ct.iter() {
                        if let Formula::AtomicFormula(AtomicFormula::Comparison(comp)) = ict {
                            if comp.equality_comparison() {
                                for ovar in outer_vars.iter() {
                                    for ivar in inner_vars.iter() {
                                        if ovar.sort == Sort::General && ivar.sort == Sort::Integer
                                        {
                                            let replacement_result =
                                                replacement_helper(ivar, ovar, comp, &formula);

                                            if replacement_result.1 {
                                                simplified_formula = replacement_result.0;
                                                replaced = true;
                                                break;
                                            }
                                        }
                                    }
                                    if replaced {
                                        break;
                                    }
                                }
                            }
                            if replaced {
                                break;
                            }
                        }
                    }
                }
                if replaced {
                    break;
                }
            }
        }

        UnboxedFormula::QuantifiedFormula {
            quantification:
                Quantification {
                    quantifier: Quantifier::Forall,
                    variables: outer_vars,
                },
            formula:
                Formula::BinaryFormula {
                    connective: BinaryConnective::Implication,
                    lhs,
                    rhs,
                },
        } => {
            if let UnboxedFormula::QuantifiedFormula {
                quantification:
                    Quantification {
                        quantifier: Quantifier::Exists,
                        variables: inner_vars,
                    },
                formula: inner_formula,
            } = lhs.unbox()
            {
                let mut replaced = false;
                let conjunctive_terms = Formula::conjoin_invert(inner_formula);
                for ct in conjunctive_terms.iter() {
                    if let Formula::AtomicFormula(AtomicFormula::Comparison(comp)) = ct {
                        if comp.equality_comparison() {
                            for ovar in outer_vars.iter() {
                                for ivar in inner_vars.iter() {
                                    if ovar.sort == Sort::General
                                        && ivar.sort == Sort::Integer
                                        && !rhs.free_variables().contains(ovar)
                                    {
                                        let replacement_result =
                                            replacement_helper(ivar, ovar, comp, &formula);
                                        if replacement_result.1 {
                                            simplified_formula = replacement_result.0;
                                            replaced = true;
                                            break;
                                        }
                                    }
                                    if replaced {
                                        break;
                                    }
                                }
                            }
                            if replaced {
                                break;
                            }
                        }
                    }
                    if replaced {
                        break;
                    }
                }
            }
        }

        _ => (),
    }
    simplified_formula
}

pub fn eliminate_redundant_quantifiers(formula: Formula) -> Formula {
    match formula.clone().unbox() {
        // Remove redundant existentials
        // e.g. exists Z$g (Z$g = X$g and F(Z$g)) => F(X$g)
        UnboxedFormula::QuantifiedFormula {
            quantification:
                Quantification {
                    quantifier: Quantifier::Exists,
                    mut variables,
                },
            formula: f,
        } => match f.clone().unbox() {
            UnboxedFormula::BinaryFormula {
                connective: BinaryConnective::Conjunction,
                ..
            } => {
                let simplification_result =
                    simplify_conjunction_tree_with_equality(f, variables.clone());
                match simplification_result.1 {
                    Some(sub_pair) => {
                        variables.retain(|v| v != &sub_pair.0);
                        Formula::QuantifiedFormula {
                            quantification: Quantification {
                                quantifier: Quantifier::Exists,
                                variables,
                            },
                            formula: simplification_result.0.into(),
                        }
                    }
                    None => formula,
                }
            }
            _ => formula,
        },

        // A universally quantified implication can sometimes be simplified
        // e.g. forall X1 .. Xj .. Xn  (F1 and .. Fi .. and Fm -> G), where Fi is Xj=t, and Xj doesn’t occur in t, and free variables occurring in t are not bound by quantifiers in F1, F2, ..
        // becomes forall X1 .. Xn  (F1 and .. and Fm -> G)
        UnboxedFormula::QuantifiedFormula {
            quantification:
                Quantification {
                    quantifier: Quantifier::Forall,
                    mut variables,
                },
            formula:
                Formula::BinaryFormula {
                    connective: BinaryConnective::Implication,
                    lhs,
                    rhs,
                },
        } => match lhs.clone().unbox() {
            UnboxedFormula::BinaryFormula {
                connective: BinaryConnective::Conjunction,
                ..
            } => {
                let mut f = formula;
                let lhs_simplify = simplify_conjunction_tree_with_equality(*lhs, variables.clone());
                match lhs_simplify.1 {
                    Some(sub_pair) => {
                        if !rhs.clone().unsafe_substitution(&sub_pair.0, &sub_pair.1) {
                            variables.retain(|v| v != &sub_pair.0);
                            f = Formula::QuantifiedFormula {
                                quantification: Quantification {
                                    quantifier: Quantifier::Forall,
                                    variables,
                                },
                                formula: Formula::BinaryFormula {
                                    connective: BinaryConnective::Implication,
                                    lhs: lhs_simplify.0.into(),
                                    rhs: rhs.substitute(sub_pair.0, sub_pair.1).into(),
                                }
                                .into(),
                            };
                        }
                        f
                    }
                    None => f,
                }
            }

            _ => formula,
        },

        _ => formula,
    }
}

pub fn simplify_transitive_equality(formula: Formula) -> Formula {
    match formula.clone().unbox() {
        // When X is a subsort of Y (or sort(X) = sort(Y)) and t is a term:
        // exists X Y (X = t and Y = t and F)
        // =>
        // exists X (X = t and F(X))
        // Replace Y with X within F
        UnboxedFormula::QuantifiedFormula {
            quantification:
                Quantification {
                    quantifier: Quantifier::Exists,
                    mut variables,
                },
            formula: f,
        } => match f.clone().unbox() {
            UnboxedFormula::BinaryFormula {
                connective: BinaryConnective::Conjunction,
                ..
            } => {
                let mut simplified = formula.clone();
                let mut simplify = false;
                let conjunctive_terms = Formula::conjoin_invert(f.clone());
                let mut ct_copy = conjunctive_terms.clone();
                for (i, ct1) in conjunctive_terms.iter().enumerate() {
                    // Search for an equality formula
                    if let Formula::AtomicFormula(AtomicFormula::Comparison(c1)) = ct1 {
                        if c1.equality_comparison() {
                            for (j, ct2) in conjunctive_terms.iter().enumerate() {
                                // Search for a second equality formula
                                if let Formula::AtomicFormula(AtomicFormula::Comparison(c2)) = ct2 {
                                    if c2.equality_comparison() && i != j {
                                        if let Some((keep_var, drop_var, drop_term)) =
                                            transitive_equality(
                                                c1.clone(),
                                                c2.clone(),
                                                variables.clone(),
                                            )
                                        {
                                            variables.retain(|x| x != &drop_var);
                                            ct_copy.retain(|t| {
                                                t != &Formula::AtomicFormula(
                                                    AtomicFormula::Comparison(drop_term.clone()),
                                                )
                                            });
                                            let keep = match keep_var.sort {
                                                Sort::General => {
                                                    GeneralTerm::Variable(keep_var.name)
                                                }
                                                Sort::Integer => GeneralTerm::IntegerTerm(
                                                    IntegerTerm::Variable(keep_var.name),
                                                ),
                                                Sort::Symbol => GeneralTerm::SymbolicTerm(
                                                    SymbolicTerm::Variable(keep_var.name),
                                                ),
                                            };
                                            let inner = Formula::conjoin(ct_copy.clone())
                                                .substitute(drop_var, keep);
                                            simplified = Formula::QuantifiedFormula {
                                                quantification: Quantification {
                                                    quantifier: Quantifier::Exists,
                                                    variables: variables.clone(),
                                                },
                                                formula: inner.into(),
                                            };
                                            simplify = true;
                                        }
                                    }
                                }
                                if simplify {
                                    break;
                                }
                            }
                        }
                    }
                    if simplify {
                        break;
                    }
                }
                simplified
            }

            _ => formula,
        },

        x => x.rebox(),
    }
}

#[cfg(test)]
mod tests {
    use {
        super::{
            eliminate_redundant_quantifiers, extend_quantifier_scope, join_nested_quantifiers,
            remove_annihilations, remove_idempotences, remove_identities,
            simplify_empty_quantifiers, simplify_formula, simplify_transitive_equality,
            simplify_variable_lists,
        },
        crate::{
            convenience::apply::Apply as _, simplifying::fol::ht::restrict_quantifier_domain,
            syntax_tree::fol::Formula,
        },
    };

    #[test]
    fn test_simplify() {
        for (src, target) in [
            ("#true and #true and a", "a"),
            ("#true and (#true and a)", "a"),
        ] {
            assert_eq!(
                simplify_formula(src.parse().unwrap()),
                target.parse().unwrap()
            )
        }
    }

    #[test]
    fn test_remove_identities() {
        for (src, target) in [
            ("#true and a", "a"),
            ("a and #true", "a"),
            ("#false or a", "a"),
            ("a or #false", "a"),
        ] {
            assert_eq!(
                src.parse::<Formula>()
                    .unwrap()
                    .apply(&mut remove_identities),
                target.parse().unwrap()
            )
        }
    }

    #[test]
    fn test_remove_annihilations() {
        for (src, target) in [
            ("#true or a", "#true"),
            ("a or #true", "#true"),
            ("#false and a", "#false"),
            ("a and #false", "#false"),
        ] {
            assert_eq!(
                src.parse::<Formula>()
                    .unwrap()
                    .apply(&mut remove_annihilations),
                target.parse().unwrap()
            )
        }
    }

    #[test]
    fn test_remove_idempotences() {
        for (src, target) in [("a and a", "a"), ("a or a", "a")] {
            assert_eq!(
                src.parse::<Formula>()
                    .unwrap()
                    .apply(&mut remove_idempotences),
                target.parse().unwrap()
            )
        }
    }

    #[test]
    fn test_join_nested_quantifiers() {
        for (src, target) in [
            ("exists X (exists Y (X = Y))", "exists X Y (X = Y)"),
            (
                "exists X Y ( exists Z ( X < Y and Y < Z ))",
                "exists X Y Z ( X < Y and Y < Z )",
            ),
            (
                "exists X (exists Y (X = Y and q(Y)))",
                "exists X Y (X = Y and q(Y))",
            ),
            (
                "exists X (exists X$i (p(X) -> X$i < 1))",
                "exists X X$i (p(X) -> X$i < 1)",
            ),
            (
                "forall X Y (forall Y Z (p(X,Y) and q(Y,Z)))",
                "forall X Y Z (p(X,Y) and q(Y,Z))",
            ),
            (
                "forall X (forall Y (forall Z (X = Y = Z)))",
                "forall X Y Z (X = Y = Z)",
            ),
        ] {
            assert_eq!(
                src.parse::<Formula>()
                    .unwrap()
                    .apply(&mut join_nested_quantifiers),
                target.parse().unwrap()
            )
        }
    }

    #[test]
    fn test_extend_quantification_scope() {
        for (src, target) in [
            (
                "exists X (q(X) and 1 < 3) and p(Z)",
                "exists X (q(X) and 1 < 3 and p(Z))",
            ),
            (
                "exists X (q(X) and 1 < 3) and p(X)",
                "exists X (q(X) and 1 < 3) and p(X)",
            ),
            (
                "forall Z X (q(X) and 1 < Z) or p(Y,Z$)",
                "forall Z X (q(X) and 1 < Z or p(Y,Z$))",
            ),
            (
                "p(Z) and exists X (q(X) and 1 < 3)",
                "exists X (p(Z) and (q(X) and 1 < 3))",
            ),
        ] {
            let result = extend_quantifier_scope(src.parse().unwrap());
            let target = target.parse().unwrap();
            assert_eq!(result, target, "{result} != {target}")
        }
    }

    #[test]
    fn test_simplify_variable_lists() {
        for (src, target) in [
            (
                "exists X Y ( q or (t and q(Y)))",
                "exists Y ( q or (t and q(Y)))",
            ),
            (
                "exists Y V ( q or forall X (t(Y) and q(X)))",
                "exists Y ( q or forall X (t(Y) and q(X)))",
            ),
        ] {
            assert_eq!(
                simplify_variable_lists(src.parse().unwrap()),
                target.parse().unwrap()
            )
        }
    }

    #[test]
    fn test_simplify_empty_quantifiers() {
        for (src, target) in [("exists Y (1 < 2)", "1 < 2"), ("forall Z #true", "#true")] {
            assert_eq!(
                simplify_empty_quantifiers(simplify_variable_lists(src.parse().unwrap())),
                target.parse().unwrap()
            )
        }
    }

    #[test]
    fn test_restrict_quantifiers() {
        for (src, target) in [
            (
                "exists Z Z1 ( exists I$i J$i ( Z = J$i and q(I$i, J$i) ) and Z = Z1 )",
                "exists Z1 J1$i ( exists I$i J$i ( J1$i = J$i and q(I$i, J$i) ) and J1$i = Z1 )",
            ),
            (
                "exists Z Z1 ( exists I$i J$i ( q(I$i, J$i) and Z = J$i) and Z = Z1 )",
                "exists Z1 J1$i ( exists I$i J$i ( q(I$i, J$i) and J1$i = J$i) and J1$i = Z1 )",
            ),
            (
                "exists Z Z1 ( Z = Z1 and exists I$i J$i ( q(I$i, J$i) and Z = J$i) )",
                "exists Z1 J1$i ( J1$i = Z1 and exists I$i J$i ( q(I$i, J$i) and J1$i = J$i) )",
            ),
            (
                "exists Z Z1 ( Z = Z1 and exists I$i J$i ( q(I$i, J$i) and Z = J$i and 3 > 2) and 1 < 5 )",
                "exists Z1 J1$i ( J1$i = Z1 and exists I$i J$i ( q(I$i, J$i) and J1$i = J$i and 3 > 2) and 1 < 5 )",
            ),
            (
                "forall X Y ( exists Z I$i (p(X) and p(Z) and Y = I$i) -> q(X) )",
                "forall X I1$i ( exists Z I$i (p(X) and p(Z) and I1$i = I$i) -> q(X) )",
            ),
            (
                "forall X Y ( exists Z I$i (p(X) and p(Z) and Y = I$i) -> q(Y) )",
                "forall X Y ( exists Z I$i (p(X) and p(Z) and Y = I$i) -> q(Y) )",
            ),
            (
                "forall X Y ( exists I$i J$i (Y = J$i and p(I$i, J$i) and I$i = X) -> q(Z) )",
                "forall X J1$i ( exists I$i J$i (J1$i = J$i and p(I$i, J$i) and I$i = X) -> q(Z) )",
            ),
            (
                "forall X Y ( exists Z I$i (p(X,Z) or Y = I$i) -> q(X) )",
                "forall X Y ( exists Z I$i (p(X,Z) or Y = I$i) -> q(X) )",
            ),
            (
                "forall X Y ( exists Z I$i (p(X,Z) and I$i = X) -> exists A X (q(A,X)) )",
                "forall Y I1$i ( exists Z I$i (p(I1$i,Z) and I$i = I1$i) -> exists A X (q(A,X)) )",
            ),
        ] {
            let src =
                restrict_quantifier_domain(src.parse().unwrap());
            let target = target.parse().unwrap();
            assert_eq!(src, target, "{src} != {target}")
        }
    }

    #[test]
    fn test_eliminate_redundant_quantifiers() {
        for (src, target) in [
            ("exists X ( X = Z and not q(X) )", "not q(Z)"),
            (
                "exists Y ( Y = X and forall V (p(Y,V) -> q(X)) )",
                "forall V (p(X,V) -> q(X))",
            ),
            (
                "exists Z Z1 ( Z = I and (exists K$i (K$i = I) and Z = Z1) )",
                "exists Z1 ( exists K$i (K$i = I) and I = Z1)",
            ),
            (
                "forall X V (p(X) and X = V -> q(V))",
                "forall V (p(V) -> q(V))",
            ),
        ] {
            let src =
                simplify_empty_quantifiers(eliminate_redundant_quantifiers(src.parse().unwrap()));
            let target = target.parse().unwrap();
            assert_eq!(src, target, "{src} != {target}")
        }
    }

    #[test]
    fn test_simplify_transitive_equality() {
        for (src, target) in [(
            "exists X Y Z ( X = 5 and Y = 5 and not p(X,Y))",
            "exists X Z ( X = 5 and not p(X,X))",
        )] {
            let src = simplify_transitive_equality(src.parse().unwrap());
            let target = target.parse().unwrap();
            assert_eq!(src, target, "{src} != {target}")
        }
    }
}
