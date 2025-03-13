use {
    crate::syntax_tree::asp::{
        Atom, AtomicFormula, BinaryOperator, Body, Comparison, Head, Program, Relation, Rule, Term,
        Variable,
    },
    lazy_static::lazy_static,
    regex::Regex,
};

lazy_static! {
    static ref RE: Regex = Regex::new(r"^V(?<number>[0-9]*)$").unwrap();
}

/// Taken from tau-star.rs
/// Choose fresh variants of `Vn` by incrementing `n`
fn choose_fresh_global_variables(program: &Program) -> Vec<Variable> {
    let mut max_arity = 0;
    let mut head_arity;
    for rule in program.rules.iter() {
        head_arity = rule.head.arity();
        if head_arity > max_arity {
            max_arity = head_arity;
        }
    }
    let mut max_taken_var = 0;
    let taken_vars = program.variables();
    for var in taken_vars {
        if let Some(caps) = RE.captures(&var.0) {
            let taken: usize = (caps["number"]).parse().unwrap_or(0);
            if taken > max_taken_var {
                max_taken_var = taken;
            }
        }
    }
    let mut globals = Vec::<Variable>::new();
    for i in 1..max_arity + 1 {
        let mut v: String = "V".to_owned();
        let counter: &str = &(max_taken_var + i).to_string();
        v.push_str(counter);
        globals.push(Variable(v));
    }
    globals
}

// fn replace_intervals_in_term_shallow<I>(term: Term, gvars: I) -> (Term, Vec<AtomicFormula>)
//     where I: Iterator
// {

//     todo!()
// }

pub fn remove_intervals_in_head(rule: Rule) -> Rule {
    let program = Program {
        rules: vec![rule.clone()],
    };
    let mut fresh_gvars = choose_fresh_global_variables(&program).into_iter();

    let mut rule_copy = rule.clone();

    match rule.head {
        Head::Basic(atom) | Head::Choice(atom) => {
            let mut new_terms = vec![];
            let mut interval_formulas = vec![];
            for term in atom.terms {
                match term {
                    Term::BinaryOperation {
                        op: BinaryOperator::Interval,
                        ..
                    } => {
                        let v = Term::Variable(fresh_gvars.next().unwrap().clone());
                        let f = AtomicFormula::Comparison(Comparison {
                            relation: Relation::Equal,
                            lhs: v.clone(),
                            rhs: term,
                        });
                        new_terms.push(v);
                        interval_formulas.push(f);
                    }
                    _ => {
                        new_terms.push(term);
                    }
                }
            }

            let new_atom = Atom {
                predicate_symbol: atom.predicate_symbol,
                terms: new_terms,
            };
            let new_head = match &rule_copy.head {
                &Head::Basic(_) => Head::Basic(new_atom),
                &Head::Choice(_) => Head::Choice(new_atom),
                &Head::Falsity => unreachable!(),
            };

            interval_formulas.append(&mut rule_copy.body.formulas);
            let new_body = Body {
                formulas: interval_formulas,
            };

            Rule {
                head: new_head,
                body: new_body,
            }
        }
        Head::Falsity => rule,
    }
}

#[cfg(test)]
mod tests {
    use {super::remove_intervals_in_head, crate::syntax_tree::asp::Rule};

    #[test]
    fn remove() {
        for (src, target) in [
            (
                "q(1..X, 1..Y) :- p(X,Y,Z).",
                "q(V1, V2) :- V1 = 1..X, V2 = 1..Y, p(X,Y,Z).",
            ),
            // ("p(2*(1..8)).", "p(2*V1) :- V1 = 1..8."),
        ] {
            let left = remove_intervals_in_head(src.parse::<Rule>().unwrap());
            let right = target.parse::<Rule>().unwrap();
            assert!(
                left == right,
                "assertion `left == right` failed:\n left:\n{left}\n right:\n{right}"
            );
        }
    }
}
