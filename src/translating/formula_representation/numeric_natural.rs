use std::fmt;

use indexmap::IndexSet;

use crate::{
    command_line::arguments::Dialect,
    syntax_tree::{
        asp::mini_gringo as asp,
        fol::sigma_0::{
            self as fol, Formula, GeneralTerm, Guard, IntegerTerm, Quantification, Sort,
            SymbolicTerm, Theory,
        },
    },
};

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct AxiomatizedTheory {
    pub axioms: Theory,
    pub theory: Theory,
}

impl From<fol::Theory> for AxiomatizedTheory {
    fn from(value: fol::Theory) -> Self {
        AxiomatizedTheory {
            axioms: fol::Theory {
                formulas: Vec::new(),
            },
            theory: value,
        }
    }
}

impl fmt::Display for AxiomatizedTheory {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.axioms.formulas.is_empty() {
            let theory = &self.theory;
            writeln!(f, "{theory}")?;
        } else {
            writeln!(f, "Axioms:")?;
            for axiom in &self.axioms {
                writeln!(f, "\t{axiom}")?;
            }
            writeln!(f, "Theory:")?;
            for formula in &self.theory {
                writeln!(f, "\t{formula}")?;
            }
        }
        Ok(())
    }
}

enum IndefiniteFunction {
    Division,
    Modulo,
    Interval,
}

// Gringo 5 (dialect D1) rounds the quotient towards 0
// Gringo 6 (dialect D0) rounds the quotient towards negative infinity
fn construct_graphf_axiom(f: IndefiniteFunction, d: Dialect) -> fol::Formula {
    match (f, d) {
        (IndefiniteFunction::Division, Dialect::GringoFive) => {
            "forall N1$ N2$ N3$ ( divisionGraphG5(N1$,N2$,N3$) <-> (
                (N1$ >= 0 and 0 <= N1$ - N2$ * N3$ < N2$) or
                (N1$ >= 0 and 0 >= N2$ * N3$ - N1$ > N2$) or
                (N1$ < 0 and 0 <= N2$ * N3$ - N1$ < N2$) or
                (N1$ < 0 and 0 >= N1$ - N2$ * N3$ > N2$)
            ))".parse().unwrap()
        },
        (IndefiniteFunction::Modulo, Dialect::GringoFive) => {
            "forall I$ J$ Z$ ( moduloGraphG5(I$,J$,Z$) <->
                exists K$ (
                    K$ * |J$| <= |I$| < (K$+1) * |J$| and
                    ((I$ * J$ >= 0 and Z$ = I$ - K$ * J$) or (I$ * J$ < 0 and Z$ = I$ + K$ * J$))))".parse().unwrap()
        },
        (IndefiniteFunction::Division, Dialect::GringoSix) => {
            "forall N1$ N2$ N3$ ( divisionGraphG6(N1$,N2$,N3$) <-> ( (0 <= N1$ - N2$ * N3$ < N2$) or (0 >= N1$ - N2$ * N3$ > N2$) ))".parse().unwrap()
        },
        (IndefiniteFunction::Modulo, Dialect::GringoSix) => {
            "forall I$ J$ R$ ( moduloGraphG6(I$,J$,R$) <-> exists Q$ (I$ = J$ * Q$ + R$ and J$ != 0 and 0 <= R$ < J$) )".parse().unwrap()
        },
        (IndefiniteFunction::Interval, _) => {
            "forall I$ J$ K$ ( intervalGraph(I$,J$,K$) <-> I$ <= K$ <= J$ )".parse().unwrap()
        },
    }
}

// Convert top-level general variables in the term to
// an integer variable of the same name if within the scope
// of an arithmetic operator.
// Keeps track of which variables have their sort changed via 'vars'
fn p2f(t: asp::Term, scope: bool, vars: &mut IndexSet<String>) -> GeneralTerm {
    match t {
        asp::Term::BasicSymbol(b) => {
            if scope {
                match b {
                    asp::BasicSymbol::Numeral(n) => {
                        GeneralTerm::IntegerTerm(IntegerTerm::Numeral(n))
                    }
                    _ => unreachable!(
                        "the only basic symbols allowed in the scope of arithmetic operators are numerals"
                    ),
                }
            } else {
                GeneralTerm::from(b)
            }
        }

        asp::Term::HerbrandFunction { symbol, terms } => {
            if scope {
                panic!("constructors should not occur within the scope of an arithmetic operation");
            }
            GeneralTerm::Function(fol::Function {
                function_symbol: symbol,
                sort: Sort::Symbol,
                terms: terms.into_iter().map(|t| p2f(t, false, vars)).collect(),
            })
        }

        asp::Term::Variable(v) => {
            if scope {
                let varname = v.0;
                vars.insert(varname.clone());
                GeneralTerm::IntegerTerm(IntegerTerm::Variable(varname))
            } else {
                GeneralTerm::Variable(v.0)
            }
        }

        asp::Term::UnaryOperation { op, arg } => {
            let gen_term = p2f(*arg, true, vars);
            let inner = match gen_term {
                GeneralTerm::IntegerTerm(integer_term) => integer_term,
                _ => unreachable!("the expression {gen_term} is not in numeric normal form"),
            };

            GeneralTerm::IntegerTerm(IntegerTerm::UnaryOperation {
                op: fol::UnaryOperator::from(op),
                arg: inner.into(),
            })
        }

        asp::Term::BinaryOperation { op, lhs, rhs } => {
            let operation = match op {
                asp::BinaryOperator::Add => fol::BinaryOperator::Add,
                asp::BinaryOperator::Subtract => fol::BinaryOperator::Subtract,
                asp::BinaryOperator::Multiply => fol::BinaryOperator::Multiply,
                _ => unreachable!(
                    "term is not in numeric normal form due to presence of indefinite functions"
                ),
            };

            let gen_lhs = p2f(*lhs, true, vars);
            let lhs = match gen_lhs {
                GeneralTerm::IntegerTerm(integer_term) => integer_term,
                _ => unreachable!("the expression {gen_lhs} is not in numeric normal form"),
            };

            let gen_rhs = p2f(*rhs, true, vars);
            let rhs = match gen_rhs {
                GeneralTerm::IntegerTerm(integer_term) => integer_term,
                _ => unreachable!("the expression {gen_rhs} is not in numeric normal form"),
            };

            GeneralTerm::IntegerTerm(IntegerTerm::BinaryOperation {
                op: operation,
                lhs: lhs.into(),
                rhs: rhs.into(),
            })
        }
    }
}

// Change the sort of every variable that occurs in
// 1) the scope of an arithmetic operation, or
// 2) the left-hand side of an equation that contains an indefinite function symbol in the right-hand side
// to the integer sort
fn nu_literal(f: asp::AtomicFormula, d: Dialect, vars: &mut IndexSet<String>) -> Formula {
    match f {
        asp::AtomicFormula::Literal(l) => {
            let sign = l.sign;
            let terms = l
                .atom
                .terms
                .into_iter()
                .map(|t| p2f(t, false, vars))
                .collect();
            let atom = Formula::AtomicFormula(fol::AtomicFormula::Atom(fol::Atom::new(
                l.atom.predicate_symbol,
                terms,
            )));

            match sign {
                asp::Sign::NoSign => atom,
                asp::Sign::Negation => Formula::UnaryFormula {
                    connective: fol::UnaryConnective::Negation,
                    formula: atom.into(),
                },
                asp::Sign::DoubleNegation => Formula::UnaryFormula {
                    connective: fol::UnaryConnective::Negation,
                    formula: Formula::UnaryFormula {
                        connective: fol::UnaryConnective::Negation,
                        formula: atom.into(),
                    }
                    .into(),
                },
            }
        }
        asp::AtomicFormula::Comparison(c) => {
            if c.clone().indefinite_equality() {
                let (binop, t1, t2) = c.rhs.destructure_binary_operation().unwrap();
                let predicate_symbol = match binop {
                    asp::BinaryOperator::Divide => match d {
                        Dialect::GringoFive => String::from("divisionGraphG5"),
                        Dialect::GringoSix => String::from("divisionGraphG6"),
                    },
                    asp::BinaryOperator::Modulo => match d {
                        Dialect::GringoFive => String::from("moduloGraphG5"),
                        Dialect::GringoSix => String::from("moduloGraphG6"),
                    },
                    asp::BinaryOperator::Interval => String::from("intervalGraph"),
                    _ => unreachable!("an indefinite equality cannot contain definite functions"),
                };
                // c.lhs is "within arithmetic scope" since it falls in case 2
                let terms = vec![
                    p2f(t1, true, vars),
                    p2f(t2, true, vars),
                    p2f(c.lhs, true, vars),
                ];
                Formula::AtomicFormula(fol::AtomicFormula::Atom(fol::Atom::new(
                    predicate_symbol,
                    terms,
                )))
            } else {
                Formula::AtomicFormula(fol::AtomicFormula::Comparison(fol::Comparison {
                    term: p2f(c.lhs, false, vars),
                    guards: vec![Guard {
                        relation: c.relation.into(),
                        term: p2f(c.rhs, false, vars),
                    }],
                }))
            }
        }
    }
}

fn nu_rule(r: asp::Rule, d: Dialect) -> Formula {
    // The set of variables from the rule whose
    // sort has been changed to "integer" in at least one term
    let mut resorted_variables = IndexSet::new();

    let body = Formula::conjoin(
        r.body
            .formulas
            .into_iter()
            .map(|f| nu_literal(f, d, &mut resorted_variables)),
    );

    let head = match r.head {
        asp::Head::Basic(atom) => nu_literal(
            asp::AtomicFormula::Literal(asp::Literal {
                sign: asp::Sign::NoSign,
                atom,
            }),
            d,
            &mut resorted_variables,
        ),
        asp::Head::Falsity => Formula::AtomicFormula(fol::AtomicFormula::Falsity),
        asp::Head::Choice(_) => {
            unreachable!("choice rules are abbreviations in numeric normal form")
        }
    };

    let partially_naturalized_rule = Formula::BinaryFormula {
        connective: fol::BinaryConnective::Implication,
        lhs: body.into(),
        rhs: head.into(),
    };

    unify_variable_sorts(partially_naturalized_rule, &resorted_variables).universal_closure()
}

fn unify_variable_sorts_term(t: GeneralTerm, vars: &IndexSet<String>) -> GeneralTerm {
    match t {
        GeneralTerm::Variable(v) => {
            if vars.contains(&v) {
                GeneralTerm::IntegerTerm(IntegerTerm::Variable(v))
            } else {
                GeneralTerm::Variable(v)
            }
        }
        GeneralTerm::SymbolicTerm(s) => match s {
            SymbolicTerm::Variable(v) => {
                if vars.contains(&v) {
                    GeneralTerm::IntegerTerm(IntegerTerm::Variable(v))
                } else {
                    GeneralTerm::SymbolicTerm(SymbolicTerm::Variable(v))
                }
            }
            x => GeneralTerm::SymbolicTerm(x),
        },
        GeneralTerm::Function(f) => GeneralTerm::Function(fol::Function {
            function_symbol: f.function_symbol,
            sort: f.sort,
            terms: f
                .terms
                .into_iter()
                .map(|t| unify_variable_sorts_term(t, vars))
                .collect(),
        }),
        x => x,
    }
}

fn unify_variable_sorts_atomic(
    f: fol::AtomicFormula,
    vars: &IndexSet<String>,
) -> fol::AtomicFormula {
    match f {
        fol::AtomicFormula::Truth => fol::AtomicFormula::Truth,
        fol::AtomicFormula::Falsity => fol::AtomicFormula::Falsity,
        fol::AtomicFormula::Atom(atom) => fol::AtomicFormula::Atom(fol::Atom::new(
            atom.predicate_symbol,
            atom.terms
                .into_iter()
                .map(|t| unify_variable_sorts_term(t, vars))
                .collect(),
        )),
        fol::AtomicFormula::Comparison(comparison) => {
            fol::AtomicFormula::Comparison(fol::Comparison {
                term: unify_variable_sorts_term(comparison.term, vars),
                guards: comparison
                    .guards
                    .into_iter()
                    .map(|g| Guard {
                        relation: g.relation,
                        term: unify_variable_sorts_term(g.term, vars),
                    })
                    .collect(),
            })
        }
    }
}

// Sets every occurrence of a variable whose name occurs in 'vars'
// to an integer-sorted variable of the same name
fn unify_variable_sorts(f: Formula, vars: &IndexSet<String>) -> Formula {
    match f {
        Formula::AtomicFormula(a) => Formula::AtomicFormula(unify_variable_sorts_atomic(a, vars)),
        Formula::UnaryFormula {
            connective,
            formula,
        } => Formula::UnaryFormula {
            connective,
            formula: unify_variable_sorts(*formula, vars).into(),
        },
        Formula::BinaryFormula {
            connective,
            lhs,
            rhs,
        } => Formula::BinaryFormula {
            connective,
            lhs: unify_variable_sorts(*lhs, vars).into(),
            rhs: unify_variable_sorts(*rhs, vars).into(),
        },
        Formula::QuantifiedFormula {
            quantification:
                Quantification {
                    quantifier,
                    variables,
                },
            formula,
        } => {
            let new_variables = variables
                .into_iter()
                .map(|v| {
                    let name = v.name.clone();
                    if vars.contains(&name) {
                        fol::Variable {
                            name,
                            sort: Sort::Integer,
                        }
                    } else {
                        v
                    }
                })
                .collect();

            Formula::QuantifiedFormula {
                quantification: Quantification {
                    quantifier,
                    variables: new_variables,
                },
                formula: unify_variable_sorts(*formula, vars).into(),
            }
        }
    }
}

// Requires a numeric normal form program as input
// Returns an (Axioms, Representation) pair
pub(crate) fn numeric_natural(p: asp::Program, d: Dialect) -> AxiomatizedTheory {
    let mut axioms = Vec::new();

    let indefinites = p.indefinite_functions();
    if indefinites.contains(&asp::BinaryOperator::Divide) {
        axioms.push(construct_graphf_axiom(IndefiniteFunction::Division, d));
    }
    if indefinites.contains(&asp::BinaryOperator::Modulo) {
        axioms.push(construct_graphf_axiom(IndefiniteFunction::Modulo, d));
    }
    if indefinites.contains(&asp::BinaryOperator::Interval) {
        axioms.push(construct_graphf_axiom(IndefiniteFunction::Interval, d));
    }

    let theory = p.rules.into_iter().map(|r| nu_rule(r, d)).collect();

    AxiomatizedTheory {
        axioms: axioms.into_iter().collect(),
        theory,
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        command_line::arguments::Dialect,
        normalizing::asp::numeric_normal::numeric_normal_form_rule,
        syntax_tree::asp::mini_gringo::Program,
        translating::formula_representation::numeric_natural::numeric_natural,
    };

    #[test]
    fn test_numeric_natural_rule() {
        for (src, target) in [
            ("q(X,Y+1) :- p(X,Y).", "forall X Y$ (p(X,Y$) -> q(X,Y$+1))."),
            (
                "q(X/Y+1) :- p(X,Y).",
                "forall V1$ X$ Y$ ( p(X$, Y$) and divisionGraphG5(X$,Y$,V1$) -> q(V1$+1) ).",
            ),
            ("p(1..8).", "forall V1$ (intervalGraph(1,8,V1$) -> p(V1$))."),
            (
                "p(a..b).",
                "forall V1$ V2$ V3$ (V1$ = a and V2$ = b and intervalGraph(V1$, V2$, V3$) -> p(V3$)).",
            ),
        ] {
            let normalized_program = Program {
                rules: vec![numeric_normal_form_rule(src.parse().unwrap())],
            };
            let src = numeric_natural(normalized_program, Dialect::GringoFive).theory;
            let target = target.parse().unwrap();
            assert_eq!(src, target, "\n{src} \n!= \n{target}")
        }
    }
}
