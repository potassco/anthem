use crate::{
    convenience::unbox::{Unbox as _, fol::sigma_0::UnboxedFormula},
    syntax_tree::fol::sigma_0::{
        Atom, AtomicFormula, BinaryConnective, Comparison, Formula, GeneralTerm, Guard,
        Quantification, Quantifier, Relation, Sort, Theory, UnaryConnective, Variable,
    },
};

// forall X ( B(X) -> forall Y (v(Y) -> p(Y)) )  ==>  forall X Y ( B(X) & v(Y) -> p(Y) )
fn move_values_to_antecedent(formula: Formula) -> Formula {
    let original = formula.clone();

    match formula.unbox() {
        // q -> forall Y (v(Y) -> p(Y))
        UnboxedFormula::BinaryFormula {
            connective: BinaryConnective::Implication,
            lhs: body,
            rhs:
                Formula::QuantifiedFormula {
                    quantification:
                        Quantification {
                            quantifier: Quantifier::Forall,
                            variables,
                        },
                    formula,
                },
        } => match formula.unbox() {
            UnboxedFormula::BinaryFormula {
                connective: BinaryConnective::Implication,
                lhs: values,
                rhs: head,
            } => Formula::QuantifiedFormula {
                quantification: Quantification {
                    quantifier: Quantifier::Forall,
                    variables,
                },
                formula: Formula::BinaryFormula {
                    connective: BinaryConnective::Implication,
                    lhs: Formula::conjoin([body, values]).into(),
                    rhs: head.into(),
                }
                .into(),
            },

            _ => original,
        },

        // forall X ( B(X) -> forall Y (v(Y) -> p(Y)) )
        UnboxedFormula::QuantifiedFormula {
            quantification:
                Quantification {
                    quantifier: Quantifier::Forall,
                    variables: outer_variables,
                },
            formula:
                Formula::BinaryFormula {
                    connective: BinaryConnective::Implication,
                    lhs: body,
                    rhs,
                },
        } => match rhs.unbox() {
            UnboxedFormula::QuantifiedFormula {
                quantification:
                    Quantification {
                        quantifier: Quantifier::Forall,
                        variables: mut inner_variables,
                    },
                formula:
                    Formula::BinaryFormula {
                        connective: BinaryConnective::Implication,
                        lhs: values,
                        rhs: head,
                    },
            } => {
                let new_implication = Formula::BinaryFormula {
                    connective: BinaryConnective::Implication,
                    lhs: Formula::conjoin([*body, *values]).into(),
                    rhs: head,
                };

                inner_variables.extend(outer_variables);

                Formula::QuantifiedFormula {
                    quantification: Quantification {
                        quantifier: Quantifier::Forall,
                        variables: inner_variables,
                    },
                    formula: new_implication.into(),
                }
            }

            _ => original,
        },

        _ => original,
    }
}

// B -> A v ~A  ==> B & ~~A -> A
fn restructure_disjunctive_head(formula: Formula) -> Formula {
    let original = formula.clone();

    match formula.unbox() {
        UnboxedFormula::BinaryFormula {
            connective: BinaryConnective::Implication,
            lhs: body,
            rhs:
                Formula::BinaryFormula {
                    connective: BinaryConnective::Disjunction,
                    lhs: atom,
                    rhs: negated_atom,
                },
        } => Formula::BinaryFormula {
            connective: BinaryConnective::Implication,
            lhs: Formula::BinaryFormula {
                connective: BinaryConnective::Conjunction,
                lhs: body.into(),
                rhs: Formula::UnaryFormula {
                    connective: UnaryConnective::Negation,
                    formula: negated_atom,
                }
                .into(),
            }
            .into(),
            rhs: atom,
        },

        UnboxedFormula::QuantifiedFormula {
            quantification:
                Quantification {
                    quantifier: Quantifier::Forall,
                    variables,
                },
            formula:
                Formula::BinaryFormula {
                    connective: BinaryConnective::Implication,
                    lhs: body,
                    rhs,
                },
        } => match rhs.unbox() {
            UnboxedFormula::BinaryFormula {
                connective: BinaryConnective::Disjunction,
                lhs: atom,
                rhs: negated_atom,
            } => Formula::QuantifiedFormula {
                quantification: Quantification {
                    quantifier: Quantifier::Forall,
                    variables,
                },
                formula: Formula::BinaryFormula {
                    connective: BinaryConnective::Implication,
                    lhs: Formula::BinaryFormula {
                        connective: BinaryConnective::Conjunction,
                        lhs: body,
                        rhs: Formula::UnaryFormula {
                            connective: UnaryConnective::Negation,
                            formula: negated_atom.into(),
                        }
                        .into(),
                    }
                    .into(),
                    rhs: atom.into(),
                }
                .into(),
            },

            _ => original,
        },

        _ => original,
    }
}

// Restructure a formula produced by a variant of nu
// into an equivalent formula of the form produced by tau-star
fn mirror_tau_star(formula: Formula) -> Formula {
    restructure_disjunctive_head(move_values_to_antecedent(formula))
}

fn make_implication_completable(
    antecedent: Formula,
    consequent: Formula,
    var_names: &[String],
) -> Option<Formula> {
    match consequent {
        Formula::AtomicFormula(AtomicFormula::Falsity) => Some(Formula::BinaryFormula {
            connective: BinaryConnective::Implication,
            lhs: antecedent.into(),
            rhs: Formula::AtomicFormula(AtomicFormula::Falsity).into(),
        }),

        // lhs -> p(t) becomes lhs & t = V -> p(V)
        Formula::AtomicFormula(AtomicFormula::Atom(atom)) => {
            let mut new_vars = vec![];
            let mut new_terms = vec![];
            let mut val_t = vec![antecedent];

            for (i, term) in atom.terms.into_iter().enumerate() {
                let var = GeneralTerm::Variable(var_names[i].clone());
                new_terms.push(var.clone());
                val_t.push(Formula::AtomicFormula(AtomicFormula::Comparison(
                    Comparison {
                        term,
                        guards: vec![Guard {
                            relation: Relation::Equal,
                            term: var,
                        }],
                    },
                )));
                new_vars.push(Variable {
                    name: var_names[i].clone(),
                    sort: Sort::General,
                });
            }

            Some(Formula::BinaryFormula {
                connective: BinaryConnective::Implication,
                lhs: Formula::conjoin(val_t).into(),
                rhs: Formula::AtomicFormula(AtomicFormula::Atom(Atom {
                    predicate_symbol: atom.predicate_symbol,
                    terms: new_terms,
                }))
                .into(),
            })
        }

        _ => None,
    }
}

// forall X ( B(X) -> p(t) )  ==>  forall X Y ( B(X) & t=Y -> p(Y) )
pub(crate) fn make_formula_completable(formula: Formula, var_names: &[String]) -> Option<Formula> {
    match mirror_tau_star(formula).unbox() {
        // lhs -> rhs
        UnboxedFormula::BinaryFormula {
            connective: BinaryConnective::Implication,
            lhs,
            rhs,
        } => make_implication_completable(lhs, rhs, var_names)
            .map(|f| f.universal_closure_with_quantifier_joining()),

        // forall X ( lhs -> rhs )
        UnboxedFormula::QuantifiedFormula {
            quantification:
                Quantification {
                    quantifier: Quantifier::Forall,
                    ..
                },
            formula:
                Formula::BinaryFormula {
                    connective: BinaryConnective::Implication,
                    lhs,
                    rhs,
                },
        } => make_implication_completable(*lhs, *rhs, var_names)
            .map(|f| f.universal_closure_with_quantifier_joining()),

        _ => None,
    }
}

/// Assumes theory is obtained by applying natural translation to a set of regular rules
/// OR by applying numeric normal form normalization followed by numeric-natural translation
pub(crate) fn make_completable(theory: Theory, var_names: &[String]) -> Option<Theory> {
    let mut formulas = Vec::<Formula>::new();

    for formula in theory.formulas {
        let f = make_formula_completable(formula, var_names)?;
        formulas.push(f);
    }

    Some(Theory { formulas })
}

pub trait MakeCompletable {
    type Output;

    fn make_completable(self, var_names: &[String]) -> Option<Self::Output>;
}

impl MakeCompletable for Theory {
    type Output = Theory;

    fn make_completable(self, var_names: &[String]) -> Option<Self::Output> {
        make_completable(self, var_names)
    }
}

#[cfg(test)]
mod tests {

    use {
        super::{move_values_to_antecedent, restructure_disjunctive_head},
        crate::{
            command_line::arguments::Dialect,
            convenience::variable_selection::VariableSelection as _,
            normalizing::{
                asp::numeric_normal::numeric_normal_form, fol::completable::make_completable,
            },
            syntax_tree::{
                asp::mini_gringo,
                fol::sigma_0::{Formula, Theory},
            },
            translating::formula_representation::numeric_natural::numeric_natural,
        },
    };

    #[test]
    fn test_move_values_to_antecedent() {
        for (source, target) in [
            ("#true -> a", "#true -> a"),
            ("forall X (#true -> p(X))", "forall X (#true -> p(X))"),
            ("b -> a", "b -> a"),
            ("forall X (q(X) -> p(X))", "forall X (q(X) -> p(X))"),
            ("forall X (X = 3 -> p(X))", "forall X (X = 3 -> p(X))"),
            (
                "forall X (X = 3 -> p(X) or not p(X))",
                "forall X (X = 3 -> p(X) or not p(X))",
            ),
            (
                "forall N0 (#true -> forall N1$i (1 <= N1$i <= 2-> p(N1$i, N0)))",
                "forall N1$i N0 (#true and 1 <= N1$i <= 2 -> p(N1$i, N0))",
            ),
            (
                "forall X$i (p(X$i) -> q(X$i + 1))",
                "forall X$i (p(X$i) -> q(X$i + 1))",
            ), // example (1) from paper [1]
            (
                "forall X Y$i Z$i (p(X, Y$i, Z$i) and X < Y$i and (1 <= Y$i <= Z$i) -> #false)",
                "forall X Y$i Z$i (p(X, Y$i, Z$i) and X < Y$i and (1 <= Y$i <= Z$i) -> #false)",
            ), // example from paper [1]
            (
                "forall X$i Y$i Z (p(X$i, Y$i, Z) -> forall N0$i N1$i (1 <= N0$i <= X$i and (1 <= N1$i <= Y$i) -> q(N0$i, N1$i)))",
                "forall N0$i N1$i X$i Y$i Z (p(X$i, Y$i, Z) and (1 <= N0$i <= X$i and (1 <= N1$i <= Y$i)) -> q(N0$i, N1$i))",
            ), //( example from paper [1]
            (
                "forall X$i Y (p(X$i, Y) -> forall N0$i (1 <= N0$i <= X$i -> q(N0$i, Y) or not q(N0$i, Y)))",
                "forall N0$i X$i Y ((p(X$i, Y) and 1 <= N0$i <= X$i) -> (q(N0$i, Y) or not q(N0$i, Y)))",
            ), // example from paper [1]
            (
                "forall X$i Y$i (1 <= X$i <= 2 and (1 <= Y$i <= 2) -> p(X$i, Y$i))",
                "forall X$i Y$i (1 <= X$i <= 2 and (1 <= Y$i <= 2) -> p(X$i, Y$i))",
            ), // example (6) from paper [2]
            (
                "forall X Y$i ( X = Y$i and (1 <= Y$i  <= 2) -> p(X, Y$i))",
                "forall X Y$i ( X = Y$i and (1 <= Y$i  <= 2) -> p(X, Y$i))",
            ), // example (7) from paper [2]
            (
                "#true -> forall N0$ N1$ ( 1 <= N0$ <= 10 and (1 <= N1$ <= 10-2) -> (h(N0$, N1$) or not h(N0$, N1$)))",
                "forall N0$ N1$ (#true and (1 <= N0$ <= 10 and (1 <= N1$ <= 10-2)) -> (h(N0$, N1$) or not h(N0$, N1$)))",
            ), // Inspired by Tiling example
            (
                "forall T$i X$i Y$i ((1 <= X$i <= 10 and (1 <= Y$i <= 10) and (1 <= T$i  <= 3)) -> (place(X$i, Y$i, T$i) or not place(X$i, Y$i, T$i)))",
                "forall T$i X$i Y$i ((1 <= X$i <= 10 and (1 <= Y$i <= 10) and (1 <= T$i  <= 3)) -> (place(X$i, Y$i, T$i) or not place(X$i, Y$i, T$i)))",
            ), // Inspired by Tiling
        ] {
            let source_formula = move_values_to_antecedent(source.parse().unwrap());
            let source = source_formula.to_string();
            let target_formula: Formula = target.parse().unwrap();
            let target = target_formula.to_string();
            assert_eq!(
                source_formula, target_formula,
                "assertion `move_values_to_antecedent` failed:\n source:\n{source:?}\n target:\n{target:?}",
            );
        }
    }

    #[test]
    fn test_restructure_disjunctive_head() {
        for (source, target) in [
            ("#true -> a", "#true -> a"),
            ("forall X (#true -> p(X))", "forall X (#true -> p(X))"),
            ("b -> a or not a", "b and not not a -> a"),
            ("forall X (q(X) -> p(X))", "forall X (q(X) -> p(X))"),
            ("forall X (X = 3 -> p(X))", "forall X (X = 3 -> p(X))"),
            (
                "forall X (X = 3 -> p(X) or not p(X))",
                "forall X (X = 3 and not not p(X) -> p(X))",
            ),
            (
                "forall N1$i N0 (#true and 1 <= N1$i <= 2 -> p(N1$i, N0))",
                "forall N1$i N0 (#true and 1 <= N1$i <= 2 -> p(N1$i, N0))",
            ),
            (
                "forall X$i (p(X$i) -> q(X$i + 1))",
                "forall X$i (p(X$i) -> q(X$i + 1))",
            ), // example (1) from paper [1]
            (
                "forall X Y$i Z$i (p(X, Y$i, Z$i) and X < Y$i and (1 <= Y$i <= Z$i) -> #false)",
                "forall X Y$i Z$i (p(X, Y$i, Z$i) and X < Y$i and (1 <= Y$i <= Z$i) -> #false)",
            ), // example from paper [1]
            (
                "forall N0$i N1$i X$i Y$i Z (p(X$i, Y$i, Z) and (1 <= N0$i <= X$i and (1 <= N1$i <= Y$i)) -> q(N0$i, N1$i))",
                "forall N0$i N1$i X$i Y$i Z (p(X$i, Y$i, Z) and (1 <= N0$i <= X$i and (1 <= N1$i <= Y$i)) -> q(N0$i, N1$i))",
            ), //( example from paper [1]
            (
                "forall N0$i X$i Y ( (p(X$i, Y) and 1 <= N0$i <= X$i) -> (q(N0$i, Y) or not q(N0$i, Y)))",
                "forall N0$i X$i Y ( (p(X$i, Y) and 1 <= N0$i <= X$i and not not q(N0$i, Y)) -> q(N0$i, Y) )",
            ), // example from paper [1]
            (
                "forall X$i Y$i (1 <= X$i <= 2 and (1 <= Y$i <= 2) -> p(X$i, Y$i))",
                "forall X$i Y$i (1 <= X$i <= 2 and (1 <= Y$i <= 2) -> p(X$i, Y$i))",
            ), // example (6) from paper [2]
            (
                "forall X Y$i ( X = Y$i and (1 <= Y$i  <= 2) -> p(X, Y$i))",
                "forall X Y$i ( X = Y$i and (1 <= Y$i  <= 2) -> p(X, Y$i))",
            ), // example (7) from paper [2]
            (
                "forall N0$ N1$ (#true and (1 <= N0$ <= 10 and (1 <= N1$ <= 10-2)) -> (h(N0$, N1$) or not h(N0$, N1$)))",
                "forall N0$ N1$ (#true and (1 <= N0$ <= 10 and (1 <= N1$ <= 10-2)) and not not h(N0$, N1$) -> h(N0$, N1$))",
            ), // Inspired by Tiling example
            (
                "forall T$i X$i Y$i ((1 <= X$i <= 10 and (1 <= Y$i <= 10) and (1 <= T$i  <= 3)) -> (place(X$i, Y$i, T$i) or not place(X$i, Y$i, T$i)))",
                "forall T$i X$i Y$i ((1 <= X$i <= 10 and (1 <= Y$i <= 10) and (1 <= T$i  <= 3) and not not place(X$i, Y$i, T$i)) -> place(X$i, Y$i, T$i))",
            ), // Inspired by Tiling
        ] {
            let source_formula = restructure_disjunctive_head(source.parse().unwrap());
            let source = source_formula.to_string();
            let target_formula: Formula = target.parse().unwrap();
            let target = target_formula.to_string();
            assert_eq!(
                source_formula, target_formula,
                "assertion `restructure_disjunctive_head` failed:\n source:\n{source:?}\n target:\n{target:?}",
            );
        }
    }

    #[test]
    fn test_make_completable() {
        for (source, target) in [
            (
                "a. p(X). p(X) :- q(X).",
                "#true -> a. forall V X (#true and X = V -> p(V)). forall V X (q(X) and X = V -> p(V))."
            ),
            (
                "p(X) :- X = 3. {p(X)} :- X = 3. p(1..2, N0).",
                "forall V X (X = 3 and X = V -> p(V)). forall V X (X = 3 and not not p(X) and X = V -> p(V)). forall N0 V V1$i V2 (intervalGraph(1, 2, V1$i) and V1$i = V and N0 = V2 -> p(V, V2))."
            ),
            (
                "q(X+1) :- p(X). :- p(X,Y,Z), X < Y, Y=1..Z.",
                "forall V X$i (p(X$i) and X$i + 1 = V -> q(V)). forall X Y$i Z$i (p(X, Y$i, Z$i) and X < Y$i and intervalGraph(1, Z$i, Y$i) -> #false)."
            ),
            (
                "q(1..X, 1..Y) :- p(X,Y,Z). p(V,Y) :- V = Y, Y = 1..2.",
                "forall V1$i V2$i V3 V4 X$i Y$i Z (p(X$i, Y$i, Z) and intervalGraph(1, X$i, V1$i) and intervalGraph(1, Y$i, V2$i) and V1$i = V3 and V2$i = V4 -> q(V3, V4)).
                forall V V3 V4 Y$i (V = Y$i and intervalGraph(1, 2, Y$i) and V = V3 and Y$i = V4 -> p(V3, V4))."
            ),
        ] {
            let source_program: mini_gringo::Program = source.parse().unwrap();
            let max_arity = source_program.max_arity();
            let natural_theory = numeric_natural(numeric_normal_form(source_program), Dialect::GringoFive).theory;

            let fresh_var_names = natural_theory
                .variables()
                .choose_fresh_variables("V", max_arity);
            let source_theory = make_completable(natural_theory, &fresh_var_names).unwrap();
            let source = source_theory.to_string();

            let target_theory: Theory = target.parse().unwrap();
            let target = target_theory.to_string();
            assert_eq!(
                source_theory, target_theory,
                "assertion `make_completable` failed:\n source:\n{source:?}\n target:\n{target:?}",
            );
        }
    }
}
