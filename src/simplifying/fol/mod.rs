pub mod classic;
pub mod ht;
pub mod intuitionistic;

use {
    crate::syntax_tree::fol::{
        Comparison, Formula, GeneralTerm, Guard, IntegerTerm, Quantification, Relation, Sort,
        Variable,
    },
    indexmap::IndexSet,
};

/// Choose `arity` variable names by incrementing `variant`, disjoint from `variables`
pub fn choose_fresh_variable_names(
    variables: &IndexSet<Variable>,
    variant: &str,
    arity: usize,
) -> Vec<String> {
    let mut taken_vars = Vec::<String>::new();
    for var in variables.iter() {
        taken_vars.push(var.name.to_string());
    }
    let mut fresh_vars = Vec::<String>::new();
    let arity_bound = match taken_vars.contains(&variant.to_string()) {
        true => arity + 1,
        false => {
            fresh_vars.push(variant.to_string());
            arity
        }
    };
    for n in 1..arity_bound {
        let mut candidate: String = variant.to_owned();
        let number: &str = &n.to_string();
        candidate.push_str(number);
        let mut m = n;
        while taken_vars.contains(&candidate) || fresh_vars.contains(&candidate) {
            variant.clone_into(&mut candidate);
            m += 1;
            let number = &m.to_string();
            candidate.push_str(number);
        }
        fresh_vars.push(candidate.to_string());
    }
    fresh_vars
}

// ASSUMES ivar is an integer variable and ovar is a general variable
// This function checks if the comparison `ivar = ovar` or `ovar = ivar` matches the comparison `comp`
// If so, it replaces ovar with a fresh integer variable within `formula`
// Otherwise it returns `formula`
fn replacement_helper(
    ivar: &Variable,
    ovar: &Variable,
    comp: &Comparison,
    formula: &Formula,
) -> (Formula, bool) {
    let mut simplified_formula = formula.clone();
    let ivar_term = GeneralTerm::IntegerTerm(IntegerTerm::Variable(ivar.name.clone()));
    let candidate = Comparison {
        term: GeneralTerm::Variable(ovar.name.clone()),
        guards: vec![Guard {
            relation: Relation::Equal,
            term: ivar_term.clone(),
        }],
    };
    let mut replace = false;
    if comp == &candidate {
        replace = true;
    } else {
        let candidate = Comparison {
            term: ivar_term.clone(),
            guards: vec![Guard {
                relation: Relation::Equal,
                term: GeneralTerm::Variable(ovar.name.clone()),
            }],
        };
        if comp == &candidate {
            replace = true;
        }
    }

    if replace {
        let varnames = choose_fresh_variable_names(
            &formula.variables(),
            &ivar.name.chars().next().unwrap().to_string(),
            1,
        );
        let fvar = varnames[0].clone();
        let fvar_term = GeneralTerm::IntegerTerm(IntegerTerm::Variable(fvar.clone()));
        match formula.clone() {
            Formula::QuantifiedFormula {
                quantification:
                    Quantification {
                        quantifier,
                        mut variables,
                    },
                formula: f,
            } => {
                variables.retain(|x| x != ovar); // Drop ovar from the outer quantification, leaving ovar free within formula
                variables.push(Variable {
                    // Add the new integer variable to replace ovar
                    name: fvar,
                    sort: Sort::Integer,
                });
                simplified_formula = Formula::QuantifiedFormula {
                    quantification: Quantification {
                        quantifier: quantifier.clone(),
                        variables,
                    },
                    formula: f.substitute(ovar.clone(), fvar_term).into(), // Replace all free occurences of ovar with fvar_term
                };
            }

            _ => panic!("You are using the replacement helper function wrong"),
        }
    }
    (simplified_formula, replace)
}
