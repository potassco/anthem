pub mod classic;
pub mod ht;
pub mod intuitionistic;

use {
    crate::syntax_tree::fol::{
        Comparison, Formula, GeneralTerm, Guard, IntegerTerm, Quantification, Relation, Sort,
        SymbolicTerm, Variable,
    },
    indexmap::IndexSet,
};

/// True if v1 is subsorteq to v2 and False otherwise
pub fn subsort(v1: &Variable, v2: &Variable) -> bool {
    match v1.sort {
        Sort::General => match v2.sort {
            Sort::General => true,
            Sort::Integer | Sort::Symbol => false,
        },
        Sort::Integer => match v2.sort {
            Sort::General | Sort::Integer => true,
            Sort::Symbol => false,
        },
        Sort::Symbol => match v2.sort {
            Sort::General | Sort::Symbol => true,
            Sort::Integer => false,
        },
    }
}

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

// Checks if two equality comparisons V1 = t1 (t1 = V1) and V2 = t2 (t2 = V2)
// satisfy that V1 is subsorteq to V2 and t1 = t2 and V1 and V2 occur in variables
// Returns keep_var, drop_var, drop_term
pub fn transitive_equality(
    c1: Comparison,
    c2: Comparison,
    variables: Vec<Variable>,
) -> Option<(Variable, Variable, Comparison)> {
    let lhs1 = c1.term.clone();
    let rhs1 = c1.guards[0].term.clone();
    let lhs2 = c2.term.clone();
    let rhs2 = c2.guards[0].term.clone();

    let is_var = |term: GeneralTerm| match term {
        GeneralTerm::Variable(ref v) => {
            let var = Variable {
                sort: Sort::General,
                name: v.to_string(),
            };
            match variables.contains(&var) {
                true => Some(var),
                false => None,
            }
        }
        GeneralTerm::IntegerTerm(IntegerTerm::Variable(ref v)) => {
            let var = Variable {
                sort: Sort::Integer,
                name: v.to_string(),
            };
            match variables.contains(&var) {
                true => Some(var),
                false => None,
            }
        }
        GeneralTerm::SymbolicTerm(SymbolicTerm::Variable(ref v)) => {
            let var = Variable {
                sort: Sort::Symbol,
                name: v.to_string(),
            };
            match variables.contains(&var) {
                true => Some(var),
                false => None,
            }
        }
        _ => None,
    };

    // Is V1 a variable?
    let lhs1_is_var = is_var(lhs1.clone());

    // Is V2 a variable?
    let lhs2_is_var = is_var(lhs2.clone());

    // Is t1 a variable?
    let rhs1_is_var = is_var(rhs1.clone());

    // Is t2 a variable?
    let rhs2_is_var = is_var(rhs2.clone());

    let mut result = None;
    match lhs1_is_var {
        Some(v1) => match lhs2_is_var {
            // v1 = rhs1
            Some(v2) => {
                // v1 = rhs1, v2 = rhs2
                if rhs1 == rhs2 {
                    if subsort(&v1, &v2) {
                        result = Some((v1, v2, c2));
                    } else if subsort(&v2, &v1) {
                        result = Some((v2, v1, c1));
                    }
                }
            }
            None => match rhs2_is_var {
                Some(v2) => {
                    // v1 = rhs1, lhs2 = v2
                    if rhs1 == lhs2 {
                        if subsort(&v1, &v2) {
                            result = Some((v1, v2, c2));
                        } else if subsort(&v2, &v1) {
                            result = Some((v2, v1, c1));
                        }
                    }
                }
                None => result = None,
            },
        },
        None => match rhs1_is_var {
            Some(v1) => {
                // lhs1 = v1
                match lhs2_is_var {
                    Some(v2) => {
                        // lhs1 = v1, v2 = rhs2
                        if lhs1 == rhs2 {
                            if subsort(&v1, &v2) {
                                result = Some((v1, v2, c2));
                            } else if subsort(&v2, &v1) {
                                result = Some((v2, v1, c1));
                            }
                        }
                    }
                    None => match rhs2_is_var {
                        Some(v2) => {
                            // lhs1 = v1, lhs2 = v2
                            if lhs1 == lhs2 {
                                if subsort(&v1, &v2) {
                                    result = Some((v1, v2, c2));
                                } else if subsort(&v2, &v1) {
                                    result = Some((v2, v1, c1));
                                }
                            }
                        }
                        None => {
                            result = None;
                        }
                    },
                }
            }
            None => {
                result = None;
            }
        },
    }
    result
}
