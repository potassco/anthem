use crate::{
    convenience::unbox::{Unbox as _, fol::UnboxedFormula},
    simplifying::fol::replacement_helper,
    syntax_tree::fol::{
        AtomicFormula, BinaryConnective, Comparison, Formula, Quantification, Quantifier, Relation,
        Sort, UnaryConnective,
    },
};

pub const CLASSIC: &[fn(Formula) -> Formula] = &[remove_double_negation];

impl Formula {
    /// Inverse function to conjoin
    pub fn conjoin_invert(formula: Formula) -> Vec<Formula> {
        match formula {
            Formula::BinaryFormula {
                connective: BinaryConnective::Conjunction,
                lhs,
                rhs,
            } => {
                let mut formulas = Self::conjoin_invert(*lhs);
                formulas.append(&mut Self::conjoin_invert(*rhs));
                formulas
            }
            _ => {
                vec![formula]
            }
        }
    }
}

impl Comparison {
    pub fn equality_comparison(&self) -> bool {
        let guards = &self.guards;
        let first = &guards[0];
        guards.len() == 1 && first.relation == Relation::Equal
    }
}

pub fn remove_double_negation(formula: Formula) -> Formula {
    // Remove double negation
    // e.g. not not F => F

    match formula.unbox() {
        UnboxedFormula::UnaryFormula {
            connective: UnaryConnective::Negation,
            formula:
                Formula::UnaryFormula {
                    connective: UnaryConnective::Negation,
                    formula: inner,
                },
        } => *inner,

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

#[cfg(test)]
mod tests {
    use {
        super::{extend_quantifier_scope, remove_double_negation, restrict_quantifier_domain},
        crate::{convenience::apply::Apply as _, syntax_tree::fol::Formula},
    };

    #[test]
    fn test_eliminate_double_negation() {
        assert_eq!(
            "not not a"
                .parse::<Formula>()
                .unwrap()
                .apply(&mut remove_double_negation),
            "a".parse().unwrap()
        )
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
            let src = restrict_quantifier_domain(src.parse().unwrap());
            let target = target.parse().unwrap();
            assert_eq!(src, target, "{src} != {target}")
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
}
