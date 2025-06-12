use crate::{
    convenience::choose_fresh_variable_names,
    syntax_tree::asp::{
        Atom, AtomicFormula, BinaryOperator, Body, Comparison, Head, Literal, PrecomputedTerm,
        Predicate, Program, Relation, Rule, Sign, Term, Variable,
    },
};
use indexmap::IndexSet;

impl Predicate {
    fn forget_successors(&self) -> Rule {
        let variables = choose_fresh_variable_names(&IndexSet::new(), "X", self.arity - 1);
        let mut terms: Vec<Term> = variables
            .into_iter()
            .map(|v| Term::Variable(Variable(v)))
            .collect();
        let head = Head::Basic(Atom {
            predicate_symbol: self.symbol.clone(),
            terms: terms.clone(),
        });

        let counter_variable = Term::Variable(Variable("N".to_string()));
        terms.push(counter_variable.clone());
        let body = Body {
            formulas: vec![
                AtomicFormula::Literal(Literal {
                    sign: Sign::NoSign,
                    atom: Atom {
                        predicate_symbol: self.symbol.clone(),
                        terms,
                    },
                }),
                AtomicFormula::Comparison(Comparison {
                    relation: Relation::GreaterEqual,
                    lhs: counter_variable,
                    rhs: Term::PrecomputedTerm(PrecomputedTerm::Numeral(0)),
                }),
            ],
        };

        Rule { head, body }
    }
}

impl Body {
    fn tighten(self, variable: Variable) -> Body {
        let mut formulas = Vec::new();
        for formula in self.formulas {
            match formula {
                AtomicFormula::Literal(Literal {
                    sign: Sign::NoSign,
                    atom,
                }) => {
                    let mut terms = atom.terms;
                    terms.push(Term::Variable(variable.clone()));
                    let atom = Atom {
                        predicate_symbol: atom.predicate_symbol,
                        terms,
                    };
                    formulas.push(AtomicFormula::Literal(Literal {
                        sign: Sign::NoSign,
                        atom,
                    }));
                }
                x => formulas.push(x),
            }
        }
        let comparison_formula = AtomicFormula::Comparison(Comparison {
            relation: Relation::GreaterEqual,
            lhs: Term::Variable(variable),
            rhs: Term::PrecomputedTerm(PrecomputedTerm::Numeral(0)),
        });
        formulas.push(comparison_formula);
        Body { formulas }
    }
}

impl Rule {
    pub fn tighten(self, variable: Variable) -> Self {
        match self.head.clone() {
            Head::Basic(a) | Head::Choice(a) => {
                let mut terms = a.terms;
                let successor = Term::BinaryOperation {
                    op: BinaryOperator::Add,
                    lhs: Term::Variable(variable.clone()).into(),
                    rhs: Term::PrecomputedTerm(PrecomputedTerm::Numeral(1)).into(),
                };
                terms.push(successor);

                let body = self.body.tighten(variable);

                let head = match self.head {
                    Head::Basic(_) => Head::Basic(Atom {
                        predicate_symbol: a.predicate_symbol,
                        terms,
                    }),
                    Head::Choice(_) => Head::Choice(Atom {
                        predicate_symbol: a.predicate_symbol,
                        terms,
                    }),
                    Head::Falsity => unreachable!(),
                };
                Rule { head, body }
            }
            Head::Falsity => self,
        }
    }
}

impl Program {
    pub fn tighten(self) -> Self {
        let predicates = self.predicates();
        let fresh_vars = choose_fresh_variable_names(&IndexSet::new(), "N", 1);
        let var = fresh_vars.first().unwrap().to_string();
        let mut rules: Vec<Rule> = self
            .rules
            .into_iter()
            .map(|r| r.tighten(Variable(var.clone())))
            .collect();
        let forgetting = predicates.into_iter().map(|p| p.forget_successors());
        rules.extend(forgetting);

        Program { rules }
    }
}
