use crate::{
    convenience::{
        apply::Apply as _,
        unbox::{fol::UnboxedFormula, Unbox as _},
    },
    syntax_tree::fol::{
        AtomicFormula, BinaryConnective, Comparison, Formula, GeneralTerm, Guard, IntegerTerm,
        Quantification, Quantifier, Relation, Sort, SymbolicTerm, Theory, Variable,
    },
};

pub fn simplify(theory: Theory) -> Theory {
    Theory {
        formulas: theory.formulas.into_iter().map(simplify_formula).collect(),
    }
}

fn simplify_formula(formula: Formula) -> Formula {
    formula.apply_all(&mut vec![
        Box::new(substitute_defined_variables),
        Box::new(evaluate_comparisons_between_equal_terms),
        Box::new(remove_identities),
        Box::new(remove_annihilations),
        Box::new(remove_idempotences),
        Box::new(remove_orphaned_variables),
        Box::new(remove_empty_quantifications),
        Box::new(join_nested_quantifiers),
    ])
}

fn substitute_defined_variables(formula: Formula) -> Formula {
    // Substitute defined variables in existential quantifications

    fn find_definition(variable: &Variable, formula: &Formula) -> Option<GeneralTerm> {
        match formula {
            Formula::AtomicFormula(AtomicFormula::Comparison(comparison)) => comparison
                .individuals()
                .filter_map(|individual| match individual {
                    (lhs, Relation::Equal, rhs) => Some((lhs, rhs)),
                    _ => None,
                })
                .flat_map(|(lhs, rhs)| [(lhs, rhs), (rhs, lhs)])
                .filter_map(|(x, term)| match (x, term, &variable.sort) {
                    (GeneralTerm::Variable(name), _, Sort::General)
                    | (
                        GeneralTerm::IntegerTerm(IntegerTerm::Variable(name)),
                        GeneralTerm::IntegerTerm(_),
                        Sort::Integer,
                    )
                    | (
                        GeneralTerm::SymbolicTerm(SymbolicTerm::Variable(name)),
                        GeneralTerm::SymbolicTerm(_),
                        Sort::Symbol,
                    ) if variable.name == *name && !term.variables().contains(variable) => {
                        Some(term)
                    }
                    _ => None,
                })
                .next()
                .cloned(),

            Formula::BinaryFormula {
                connective: BinaryConnective::Conjunction,
                lhs,
                rhs,
            } => find_definition(variable, lhs).or_else(|| find_definition(variable, rhs)),

            _ => None,
        }
    }

    match formula {
        Formula::QuantifiedFormula {
            quantification:
                Quantification {
                    quantifier: quantifier @ Quantifier::Exists,
                    variables,
                },
            formula,
        } => {
            let mut formula = *formula;

            for variable in variables.iter().rev() {
                if let Some(definition) = find_definition(variable, &formula) {
                    formula = formula.substitute(variable.clone(), definition);
                }
            }

            Formula::quantify(formula, quantifier, variables)
        }
        x => x,
    }
}

fn evaluate_comparisons_between_equal_terms(formula: Formula) -> Formula {
    // Evaluate comparisons between structurally equal terms
    // e.g. T  = T => #true
    // e.g. T != T => #false
    // e.g. T1 = T2 = T3 => T1 = T2 and T2 = T3 (side effect)

    match formula {
        Formula::AtomicFormula(AtomicFormula::Comparison(Comparison { term, guards })) => {
            let mut formulas = vec![];

            let mut lhs = term;
            for Guard {
                relation,
                term: rhs,
            } in guards
            {
                formulas.push(Formula::AtomicFormula(if lhs == rhs {
                    match relation {
                        // T  = T => #true
                        // T >= T => #true
                        // T <= T => #true
                        Relation::Equal | Relation::GreaterEqual | Relation::LessEqual => {
                            AtomicFormula::Truth
                        }
                        // T != T => #false
                        // T >  T => #false
                        // T <  T => #false
                        Relation::NotEqual | Relation::Greater | Relation::Less => {
                            AtomicFormula::Falsity
                        }
                    }
                } else {
                    AtomicFormula::Comparison(Comparison {
                        term: lhs,
                        guards: vec![Guard {
                            relation,
                            term: rhs.clone(),
                        }],
                    })
                }));

                lhs = rhs;
            }

            Formula::conjoin(formulas)
        }
        x => x,
    }
}

fn remove_identities(formula: Formula) -> Formula {
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

fn remove_annihilations(formula: Formula) -> Formula {
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

fn remove_idempotences(formula: Formula) -> Formula {
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

fn remove_orphaned_variables(formula: Formula) -> Formula {
    // Remove orphaned variables in quantification
    // e.g. q X Y F(X) => q X F(X)

    match formula {
        // forall X Y F(X) => forall X F(X)
        // exists X Y F(X) => exists X F(X)
        Formula::QuantifiedFormula {
            quantification:
                Quantification {
                    quantifier,
                    variables,
                },
            formula,
        } => {
            let free_variables = formula.free_variables();
            let variables = variables
                .into_iter()
                .filter(|v| free_variables.contains(v))
                .collect();

            Formula::QuantifiedFormula {
                quantification: Quantification {
                    quantifier,
                    variables,
                },
                formula,
            }
        }
        x => x,
    }
}

fn remove_empty_quantifications(formula: Formula) -> Formula {
    // Remove empty quantifiers
    // e.g. q F => F

    match formula {
        // forall F => F
        // exists F => F
        Formula::QuantifiedFormula {
            quantification,
            formula,
        } if quantification.variables.is_empty() => *formula,
        x => x,
    }
}

pub(crate) fn join_nested_quantifiers(formula: Formula) -> Formula {
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

#[cfg(test)]
mod tests {
    use {
        super::{
            evaluate_comparisons_between_equal_terms, join_nested_quantifiers,
            remove_annihilations, remove_idempotences, remove_identities,
            remove_orphaned_variables, simplify_formula,
        },
        crate::{
            convenience::apply::Apply as _,
            simplifying::fol::ht::{remove_empty_quantifications, substitute_defined_variables},
            syntax_tree::fol::Formula,
        },
    };

    #[test]
    fn test_substitute_defined_variables() {
        for (src, target) in [
            (
                "exists X$g (X$g = 1 and p(X$g))",
                "exists X$g (1 = 1 and p(1))",
            ),
            (
                "exists X$g (X$g = a and p(X$g))",
                "exists X$g (a = a and p(a))",
            ),
            (
                "exists X$i (X$i = 1 and p(X$i))",
                "exists X$i (1 = 1 and p(1))",
            ),
            (
                "exists X$i (X$i = a and p(X$i))",
                "exists X$i (X$i = a and p(X$i))",
            ),
            (
                "exists X$s (X$s = 1 and p(X$s))",
                "exists X$s (X$s = 1 and p(X$s))",
            ),
            (
                "exists X$s (X$s = a and p(X$s))",
                "exists X$s (a = a and p(a))",
            ),
            (
                "exists X$i (X$i = X$i + 1 and p(X$i))",
                "exists X$i (X$i = X$i + 1 and p(X$i))",
            ),
            (
                "exists X$i (X$i = 1 or p(X$i))",
                "exists X$i (X$i = 1 or p(X$i))",
            ),
            (
                "forall X$i (X$i = 1 and p(X$i))",
                "forall X$i (X$i = 1 and p(X$i))",
            ),
        ] {
            assert_eq!(
                src.parse::<Formula>()
                    .unwrap()
                    .apply(&mut substitute_defined_variables),
                target.parse().unwrap()
            )
        }
    }

    #[test]
    fn test_simplify() {
        for (src, target) in [
            ("#true and #true and a", "a"),
            ("#true and (#true and a)", "a"),
            ("forall X a", "a"),
            ("X = X and a", "a"),
            ("forall X (X = X)", "#true"),
        ] {
            assert_eq!(
                simplify_formula(src.parse().unwrap()),
                target.parse().unwrap()
            )
        }
    }

    #[test]
    fn test_evaluate_comparisons_between_equal_terms() {
        for (src, target) in [
            ("X = X", "#true"),
            ("X = Y", "X = Y"),
            ("X != X", "#false"),
            ("X != Y", "X != Y"),
            ("X > X", "#false"),
            ("X > Y", "X > Y"),
            ("X < X", "#false"),
            ("X < Y", "X < Y"),
            ("X >= X", "#true"),
            ("X >= Y", "X >= Y"),
            ("X <= X", "#true"),
            ("X <= Y", "X <= Y"),
            ("X$i + 1 = X$i + 1", "#true"),
            ("X$i + 1 + 1 = X$i + 2", "X$i + 1 + 1 = X$i + 2"),
            ("X = X = Y", "#true and X = Y"),
            ("X != X = Y", "#false and X = Y"),
            ("X = Y = Z", "X = Y and Y = Z"),
        ] {
            assert_eq!(
                src.parse::<Formula>()
                    .unwrap()
                    .apply(&mut evaluate_comparisons_between_equal_terms),
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
    fn test_remove_orphaned_variables() {
        for (src, target) in [
            ("forall X Y Z (X = X)", "forall X (X = X)"),
            ("exists X Y (X = Y)", "exists X Y (X = Y)"),
            ("exists X Y Z (X = Y)", "exists X Y (X = Y)"),
        ] {
            assert_eq!(
                src.parse::<Formula>()
                    .unwrap()
                    .apply(&mut remove_orphaned_variables),
                target.parse().unwrap()
            )
        }
    }

    #[test]
    fn test_remove_empty_quantifications() {
        use crate::syntax_tree::fol::{Atom, AtomicFormula, Quantification, Quantifier};

        let src = Formula::QuantifiedFormula {
            quantification: Quantification {
                quantifier: Quantifier::Forall,
                variables: vec![],
            },
            formula: Box::new(Formula::AtomicFormula(AtomicFormula::Atom(Atom {
                predicate_symbol: "a".into(),
                terms: vec![],
            }))),
        };

        let target = Formula::AtomicFormula(AtomicFormula::Atom(Atom {
            predicate_symbol: "a".into(),
            terms: vec![],
        }));

        assert_eq!(src.apply(&mut remove_empty_quantifications), target);
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
}
