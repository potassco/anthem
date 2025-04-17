use crate::{
    convenience::unbox::{Unbox as _, fol::UnboxedFormula},
    syntax_tree::fol::{
        AtomicFormula, BinaryConnective, Formula, GeneralTerm, IntegerTerm, Quantification,
        Quantifier, Relation, Sort, SymbolicTerm, UnaryConnective, Variable,
    },
};

pub const CLASSIC: &[fn(Formula) -> Formula] =
    &[remove_double_negation, substitute_defined_variables];

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

pub fn substitute_defined_variables(formula: Formula) -> Formula {
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

#[cfg(test)]
mod tests {
    use {
        super::{remove_double_negation, substitute_defined_variables},
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
}
