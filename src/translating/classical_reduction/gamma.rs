use crate::{
    convenience::apply::Apply as _,
    syntax_tree::fol::{AtomicFormula, BinaryConnective, Formula, Theory, UnaryConnective},
};

pub fn gamma(theory: Theory) -> Theory {
    let mut formulas = Vec::new();
    for formula in theory.formulas {
        formulas.push(gamma_formula(formula));
    }

    Theory { formulas }
}

pub fn gamma_formula(formula: Formula) -> Formula {
    match formula {
        x @ Formula::AtomicFormula(_) => here(x),

        Formula::UnaryFormula {
            connective: connective @ UnaryConnective::Negation,
            formula,
        } => Formula::UnaryFormula {
            connective,
            formula: there(*formula).into(),
        },

        Formula::BinaryFormula {
            connective:
                connective @ BinaryConnective::Conjunction | connective @ BinaryConnective::Disjunction,
            lhs,
            rhs,
        } => Formula::BinaryFormula {
            connective,
            lhs: gamma_formula(*lhs).into(),
            rhs: gamma_formula(*rhs).into(),
        },

        Formula::BinaryFormula {
            connective:
                connective @ BinaryConnective::Implication
                | connective @ BinaryConnective::ReverseImplication
                | connective @ BinaryConnective::Equivalence,
            lhs,
            rhs,
        } => Formula::BinaryFormula {
            connective: BinaryConnective::Conjunction,
            lhs: Formula::BinaryFormula {
                connective: connective.clone(),
                lhs: gamma_formula(*lhs.clone()).into(),
                rhs: gamma_formula(*rhs.clone()).into(),
            }
            .into(),
            rhs: Formula::BinaryFormula {
                connective,
                lhs: there(*lhs).into(),
                rhs: there(*rhs).into(),
            }
            .into(),
        },

        Formula::QuantifiedFormula {
            quantification,
            formula,
        } => Formula::QuantifiedFormula {
            quantification,
            formula: gamma_formula(*formula).into(),
        },
    }
}

pub fn here(formula: Formula) -> Formula {
    prepend_predicate(formula, "h")
}

pub fn there(formula: Formula) -> Formula {
    prepend_predicate(formula, "t")
}

fn prepend_predicate(formula: Formula, prefix: &'static str) -> Formula {
    formula.apply(&mut |formula| match formula {
        Formula::AtomicFormula(AtomicFormula::Atom(mut a)) => {
            a.predicate_symbol.insert_str(0, prefix);
            Formula::AtomicFormula(AtomicFormula::Atom(a))
        }
        x => x,
    })
}

#[cfg(test)]
mod tests {
    use super::gamma_formula;

    #[test]
    fn test_gamma() {
        for (src, target) in [
            ("#true", "#true"),
            ("a", "ha"),
            ("a(a)", "ha(a)"),
            ("X > 1", "X > 1"),
            ("not a", "not ta"),
            ("not X > 1", "not X > 1"),
            ("a and not b", "ha and not tb"),
            ("a or not b", "ha or not tb"),
            ("a -> b", "(ha -> hb) and (ta -> tb)"),
            ("a <- b", "(ha <- hb) and (ta <- tb)"),
            ("a <-> b", "(ha <-> hb) and (ta <-> tb)"),
            ("forall X p(X)", "forall X hp(X)"),
            ("exists X p(X)", "exists X hp(X)"),
        ] {
            let left = gamma_formula(src.parse().unwrap());
            let right = target.parse().unwrap();

            assert!(
                left == right,
                "assertion `left == right` failed:\n left:\n{left}\n right:\n{right}"
            );
        }
    }
}
