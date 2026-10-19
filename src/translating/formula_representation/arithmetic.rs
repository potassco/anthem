use crate::{
    command_line::arguments::Dialect,
    convenience::fresh_names::FreshVariables as _,
    syntax_tree::{
        asp::mini_gringo as asp,
        fol::sigma_0::{Formula, GeneralTerm, IntegerTerm, Sort, Variable},
    },
};

/// The arithmetic function symbols of mini-gringo that are not total functions on the integers
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
pub(crate) enum IndefiniteFunction {
    Division,
    Modulo,
    Interval,
}

impl TryFrom<asp::BinaryOperator> for IndefiniteFunction {
    type Error = asp::BinaryOperator;

    fn try_from(op: asp::BinaryOperator) -> Result<Self, Self::Error> {
        match op {
            asp::BinaryOperator::Divide => Ok(IndefiniteFunction::Division),
            asp::BinaryOperator::Modulo => Ok(IndefiniteFunction::Modulo),
            asp::BinaryOperator::Interval => Ok(IndefiniteFunction::Interval),
            op @ (asp::BinaryOperator::Add
            | asp::BinaryOperator::Subtract
            | asp::BinaryOperator::Multiply) => Err(op),
        }
    }
}

// A formula F(N1, N2, N3) defining the indefinite function f, i.e.,
// N3 is a value of f(N1, N2) iff F(N1, N2, N3) holds
// (Fandinno, Lierler, and Lifschitz, A Normal Form for Rules Containing Arithmetic Operations, 2026)
// Gringo 5 rounds the quotient towards 0, the remainder has the sign of the dividend
// Gringo 6 rounds the quotient towards negative infinity, the remainder has the sign of the divisor
fn defining_formula_template(f: IndefiniteFunction, d: Dialect) -> Formula {
    match (f, d) {
        (IndefiniteFunction::Division, Dialect::GringoFive) => {
            "(N1$ >= 0 and 0 <= N1$ - N2$ * N3$ < N2$) or
             (N1$ >= 0 and 0 >= N2$ * N3$ - N1$ > N2$) or
             (N1$ < 0 and 0 <= N2$ * N3$ - N1$ < N2$) or
             (N1$ < 0 and 0 >= N1$ - N2$ * N3$ > N2$)"
                .parse()
                .unwrap()
        }
        (IndefiniteFunction::Modulo, Dialect::GringoFive) => {
            "exists K$ (
                K$ * |N2$| <= |N1$| < (K$ + 1) * |N2$| and
                ((N1$ * N2$ >= 0 and N3$ = N1$ - K$ * N2$) or (N1$ * N2$ < 0 and N3$ = N1$ + K$ * N2$)))"
                .parse()
                .unwrap()
        }
        (IndefiniteFunction::Division, Dialect::GringoSix) => {
            "(0 <= N1$ - N2$ * N3$ < N2$) or (0 >= N1$ - N2$ * N3$ > N2$)"
                .parse()
                .unwrap()
        }
        (IndefiniteFunction::Modulo, Dialect::GringoSix) => {
            "exists Q$ (N1$ = N2$ * Q$ + N3$ and (0 <= N3$ < N2$ or N2$ < N3$ <= 0))"
                .parse()
                .unwrap()
        }
        (IndefiniteFunction::Interval, _) => "N1$ <= N3$ <= N2$".parse().unwrap(),
    }
}

/// F(t1, t2, t3) for the formula F defining the indefinite function f in dialect d,
/// i.e., a formula expressing that t3 is a value of f(t1, t2)
pub(crate) fn defining_formula(
    f: IndefiniteFunction,
    d: Dialect,
    args: [IntegerTerm; 3],
) -> Formula {
    let template = defining_formula_template(f, d);

    let parameters = ["N1", "N2", "N3"].map(|name| Variable {
        name: name.into(),
        sort: Sort::Integer,
    });

    // Rename the parameters apart from the variables of the arguments first,
    // so substituting the arguments one after another cannot capture any of them
    let mut taken_vars = template.variables();
    for arg in &args {
        taken_vars.extend(arg.variables());
    }

    let mut formula = template;
    let mut fresh_parameters = Vec::new();
    for parameter in parameters {
        let fresh = Variable {
            name: taken_vars.choose_fresh_variable(&parameter.name),
            sort: Sort::Integer,
        };
        taken_vars.insert(fresh.clone());
        formula = formula.substitute(parameter, fresh.clone().into());
        fresh_parameters.push(fresh);
    }

    for (parameter, arg) in fresh_parameters.into_iter().zip(args) {
        formula = formula.substitute(parameter, GeneralTerm::IntegerTerm(arg));
    }

    formula
}

#[cfg(test)]
mod tests {
    use {
        super::{IndefiniteFunction, defining_formula},
        crate::{command_line::arguments::Dialect, syntax_tree::fol::sigma_0::Formula},
    };

    #[test]
    fn test_defining_formula() {
        for (f, d, args, target) in [
            (
                IndefiniteFunction::Division,
                Dialect::GringoFive,
                ["X$", "Y$", "Z$"],
                "(X$ >= 0 and 0 <= X$ - Y$ * Z$ < Y$) or (X$ >= 0 and 0 >= Y$ * Z$ - X$ > Y$) or (X$ < 0 and 0 <= Y$ * Z$ - X$ < Y$) or (X$ < 0 and 0 >= X$ - Y$ * Z$ > Y$)",
            ),
            (
                IndefiniteFunction::Modulo,
                Dialect::GringoFive,
                ["X$", "Y$", "Z$"],
                "exists K$ (K$ * |Y$| <= |X$| < (K$ + 1) * |Y$| and ((X$ * Y$ >= 0 and Z$ = X$ - K$ * Y$) or (X$ * Y$ < 0 and Z$ = X$ + K$ * Y$)))",
            ),
            (
                IndefiniteFunction::Interval,
                Dialect::GringoFive,
                ["X$", "Y$", "Z$"],
                "X$ <= Z$ <= Y$",
            ),
            (
                IndefiniteFunction::Division,
                Dialect::GringoSix,
                ["X$", "Y$", "Z$"],
                "(0 <= X$ - Y$ * Z$ < Y$) or (0 >= X$ - Y$ * Z$ > Y$)",
            ),
            (
                IndefiniteFunction::Modulo,
                Dialect::GringoSix,
                ["X$", "Y$", "Z$"],
                "exists Q$ (X$ = Y$ * Q$ + Z$ and (0 <= Z$ < Y$ or Y$ < Z$ <= 0))",
            ),
            (
                IndefiniteFunction::Interval,
                Dialect::GringoSix,
                ["X$", "Y$", "Z$"],
                "X$ <= Z$ <= Y$",
            ),
            (
                IndefiniteFunction::Division,
                Dialect::GringoSix,
                ["X$ + 1", "2", "V$"],
                "(0 <= X$ + 1 - 2 * V$ < 2) or (0 >= X$ + 1 - 2 * V$ > 2)",
            ),
            (
                IndefiniteFunction::Interval,
                Dialect::GringoSix,
                ["N2$", "N1$", "N3$"],
                "N2$ <= N3$ <= N1$",
            ),
            (
                IndefiniteFunction::Modulo,
                Dialect::GringoSix,
                ["Q$", "N1$", "K$"],
                "exists Q1$ (Q$ = N1$ * Q1$ + K$ and (0 <= K$ < N1$ or N1$ < K$ <= 0))",
            ),
        ] {
            let left = defining_formula(f, d, args.map(|arg| arg.parse().unwrap()));
            let right: Formula = target.parse().unwrap();
            assert!(
                left == right,
                "assertion `left == right` failed:\n left:\n{left}\n right:\n{right}"
            );
        }
    }
}
