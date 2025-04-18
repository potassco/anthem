use crate::{
    convenience::unbox::{Unbox as _, fol::UnboxedFormula},
    syntax_tree::fol::{
        AtomicFormula, BinaryConnective, Formula, GeneralTerm, IntegerTerm, Quantification,
        Quantifier, Relation, Sort, SymbolicTerm, UnaryConnective, Variable,
    },
};

pub const CLASSIC: &[fn(Formula) -> Formula] = &[
    remove_double_negation,
    substitute_defined_variables,
    //unstable::eliminate_redundant_quantifiers,
    super::intuitionistic::remove_orphaned_variables,
    super::intuitionistic::remove_empty_quantifications,
    unstable::restrict_quantifier_domain,
    super::intuitionistic::remove_orphaned_variables,
    super::intuitionistic::remove_empty_quantifications,
    unstable::extend_quantifier_scope,
    super::intuitionistic::remove_orphaned_variables,
    super::intuitionistic::remove_empty_quantifications,
    unstable::simplify_transitive_equality,
    super::intuitionistic::remove_orphaned_variables,
    super::intuitionistic::remove_empty_quantifications,
];

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
            // (
            //     "exists I$i J$i K$i (I$i = 0 and exists I$i J1$i (J$i = I$i - J1$i and I$i = h$i and J1$i = 1))",
            //     "p(a)",
            // ),
        ] {
            let src = src
                .parse::<Formula>()
                .unwrap()
                .apply(&mut substitute_defined_variables);
            let target = target.parse().unwrap();
            assert_eq!(src, target, "\n{src} \n!= {target}")
        }
    }
}

pub mod unstable {
    use {
        crate::{
            convenience::unbox::{Unbox as _, fol::UnboxedFormula},
            syntax_tree::fol::{
                AtomicFormula, BinaryConnective, Comparison, Formula, GeneralTerm, Guard,
                IntegerTerm, Quantification, Quantifier, Relation, Sort, SymbolicTerm, Variable,
            },
        },
        indexmap::IndexSet,
    };

    /// True if v1 is subsorteq to v2 and False otherwise
    fn subsort(v1: &Variable, v2: &Variable) -> bool {
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
    fn choose_fresh_variable_names(
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
    fn transitive_equality(
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

    /// Inverse function to conjoin
    fn conjoin_invert(formula: Formula) -> Vec<Formula> {
        match formula {
            Formula::BinaryFormula {
                connective: BinaryConnective::Conjunction,
                lhs,
                rhs,
            } => {
                let mut formulas = conjoin_invert(*lhs);
                formulas.append(&mut conjoin_invert(*rhs));
                formulas
            }
            _ => {
                vec![formula]
            }
        }
    }

    fn equality_comparison(comparsion: &Comparison) -> bool {
        let guards = &comparsion.guards;
        let first = &guards[0];
        guards.len() == 1 && first.relation == Relation::Equal
    }

    // ASSUMES formula has the form:
    // F(var) & var = term  OR
    // F(var) & term = var
    // If var is a variable of sort S and term is a term of a subsort of S,
    // and term doesn't contain variables quantified within F, return `F(term)`
    // Otherwise, return the original formula
    fn subsort_equality(var: Variable, term: GeneralTerm, formula: Formula) -> (Formula, bool) {
        let mut modified = false;
        let mut simplified_formula = formula.clone();
        match formula.clone().unbox() {
            UnboxedFormula::BinaryFormula {
                connective: BinaryConnective::Conjunction,
                lhs,
                ..
            } => {
                let term_vars = term.variables(); // term must not contain var
                match var.sort {
                    Sort::General => {
                        if !term_vars.contains(&var)
                            && !lhs.clone().unsafe_substitution(&var, &term)
                        {
                            modified = true;
                            simplified_formula = lhs.substitute(var, term);
                        }
                    }
                    Sort::Integer => match term.clone() {
                        GeneralTerm::IntegerTerm(_) => {
                            if !term_vars.contains(&var)
                                && !lhs.clone().unsafe_substitution(&var, &term)
                            {
                                modified = true;
                                simplified_formula = lhs.substitute(var, term);
                            }
                        }
                        _ => {
                            simplified_formula = formula;
                        }
                    },
                    Sort::Symbol => match term.clone() {
                        GeneralTerm::SymbolicTerm(_) => {
                            if !term_vars.contains(&var)
                                && !lhs.clone().unsafe_substitution(&var, &term)
                            {
                                modified = true;
                                simplified_formula = lhs.substitute(var, term);
                            }
                        }
                        _ => {
                            simplified_formula = formula;
                        }
                    },
                }
            }

            _ => panic!("you're using the subsort equality fn wrong"),
        }
        (simplified_formula, modified)
    }

    // Given a tree of conjunctions, F1, .. Fi, .. Fn, identify an equality formula Fi: X = t or t = X
    // If possible, substitute t for X within the tree and drop Fi
    // Return the original formula and None if not possible
    // Otherwise, return the simplified formula and the (X, t) substitution pair
    fn simplify_conjunction_tree_with_equality(
        formula: Formula,
        enclosing_variables: Vec<Variable>,
    ) -> (Formula, Option<(Variable, GeneralTerm)>) {
        let mut result = (formula.clone(), None);
        let conjunctive_terms = conjoin_invert(formula.clone());
        for ct in conjunctive_terms.iter() {
            // Search for an equality formula
            if let Formula::AtomicFormula(AtomicFormula::Comparison(comp)) = ct {
                if equality_comparison(comp) {
                    let term = &comp.term;
                    let g = comp.guards[0].clone();
                    let lhs_is_var = match term.clone() {
                        GeneralTerm::Variable(v) => Some(Variable {
                            sort: Sort::General,
                            name: v,
                        }),
                        GeneralTerm::IntegerTerm(IntegerTerm::Variable(v)) => Some(Variable {
                            sort: Sort::Integer,
                            name: v,
                        }),
                        GeneralTerm::SymbolicTerm(SymbolicTerm::Variable(v)) => Some(Variable {
                            sort: Sort::Symbol,
                            name: v,
                        }),
                        _ => None,
                    };
                    let rhs_is_var = match g.term.clone() {
                        GeneralTerm::Variable(v) => Some(Variable {
                            sort: Sort::General,
                            name: v,
                        }),
                        GeneralTerm::IntegerTerm(IntegerTerm::Variable(v)) => Some(Variable {
                            sort: Sort::Integer,
                            name: v,
                        }),
                        GeneralTerm::SymbolicTerm(SymbolicTerm::Variable(v)) => Some(Variable {
                            sort: Sort::Symbol,
                            name: v,
                        }),
                        _ => None,
                    };

                    let mut safety = true; // Simplify var = term or term = var but not both
                    // Don't restructure the conjunction tree unless simplification occurs
                    let mut restructured = vec![]; // Make the equality formula the top rhs leaf of a new conjunction tree
                    // for i in 0..conjunctive_terms.len() {
                    //     if conjunctive_terms[i] != *ct {
                    //         restructured.push(conjunctive_terms[i].clone());
                    //     }
                    // }
                    for alt_ct in conjunctive_terms.clone() {
                        if alt_ct != *ct {
                            restructured.push(alt_ct);
                        }
                    }
                    restructured.push(ct.clone());

                    let simplified = Formula::conjoin(restructured);

                    if let Some(v1) = lhs_is_var {
                        if enclosing_variables.contains(&v1) {
                            let simplification_result =
                                subsort_equality(v1.clone(), g.term.clone(), simplified.clone());
                            if simplification_result.1 {
                                result = (simplification_result.0, Some((v1, g.term)));
                                safety = false;
                            }
                        }
                    }
                    if let Some(v2) = rhs_is_var {
                        if enclosing_variables.contains(&v2) && safety {
                            let simplification_result =
                                subsort_equality(v2.clone(), term.clone(), simplified);
                            if simplification_result.1 {
                                result = (simplification_result.0, Some((v2, term.clone())));
                                safety = false;
                            }
                        }
                    }
                    if !safety {
                        break;
                    }
                }
            }
        }
        result
    }

    pub(crate) fn restrict_quantifier_domain(formula: Formula) -> Formula {
        let mut simplified_formula = formula.clone();
        match formula.clone().unbox() {
            // Replace a general variable in an outer quantification with a fresh integer variable capturing an inner quantification
            // e.g. exists Z$g (exists I$i J$i (I$i = Z$g & G) & H) => exists K$i (exists I$i J$i (I$i = K$i & G) & H)
            // or  forall Z$g (exists I$i J$i (I$i = Z$g & G) -> H) => forall K$i (exists I$i J$i (I$i = K$i & G) -> H)
            UnboxedFormula::QuantifiedFormula {
                quantification:
                    Quantification {
                        quantifier: Quantifier::Exists,
                        variables: outer_vars,
                    },
                formula:
                    Formula::BinaryFormula {
                        connective: BinaryConnective::Conjunction,
                        lhs,
                        rhs,
                    },
            } => {
                let mut replaced = false;
                let mut conjunctive_terms = conjoin_invert(*lhs);
                conjunctive_terms.extend(conjoin_invert(*rhs));
                for ct in conjunctive_terms.iter() {
                    if let Formula::QuantifiedFormula {
                        quantification:
                            Quantification {
                                quantifier: Quantifier::Exists,
                                variables: inner_vars,
                            },
                        formula: inner_formula,
                    } = ct
                    {
                        let inner_ct = conjoin_invert(*inner_formula.clone());
                        for ict in inner_ct.iter() {
                            if let Formula::AtomicFormula(AtomicFormula::Comparison(comp)) = ict {
                                if equality_comparison(comp) {
                                    for ovar in outer_vars.iter() {
                                        for ivar in inner_vars.iter() {
                                            if ovar.sort == Sort::General
                                                && ivar.sort == Sort::Integer
                                            {
                                                let replacement_result =
                                                    replacement_helper(ivar, ovar, comp, &formula);

                                                if replacement_result.1 {
                                                    simplified_formula = replacement_result.0;
                                                    replaced = true;
                                                    break;
                                                }
                                            }
                                        }
                                        if replaced {
                                            break;
                                        }
                                    }
                                }
                                if replaced {
                                    break;
                                }
                            }
                        }
                    }
                    if replaced {
                        break;
                    }
                }
            }

            UnboxedFormula::QuantifiedFormula {
                quantification:
                    Quantification {
                        quantifier: Quantifier::Forall,
                        variables: outer_vars,
                    },
                formula:
                    Formula::BinaryFormula {
                        connective: BinaryConnective::Implication,
                        lhs,
                        rhs,
                    },
            } => {
                if let UnboxedFormula::QuantifiedFormula {
                    quantification:
                        Quantification {
                            quantifier: Quantifier::Exists,
                            variables: inner_vars,
                        },
                    formula: inner_formula,
                } = lhs.unbox()
                {
                    let mut replaced = false;
                    let conjunctive_terms = conjoin_invert(inner_formula);
                    for ct in conjunctive_terms.iter() {
                        if let Formula::AtomicFormula(AtomicFormula::Comparison(comp)) = ct {
                            if equality_comparison(comp) {
                                for ovar in outer_vars.iter() {
                                    for ivar in inner_vars.iter() {
                                        if ovar.sort == Sort::General
                                            && ivar.sort == Sort::Integer
                                            && !rhs.free_variables().contains(ovar)
                                        {
                                            let replacement_result =
                                                replacement_helper(ivar, ovar, comp, &formula);
                                            if replacement_result.1 {
                                                simplified_formula = replacement_result.0;
                                                replaced = true;
                                                break;
                                            }
                                        }
                                        if replaced {
                                            break;
                                        }
                                    }
                                }
                                if replaced {
                                    break;
                                }
                            }
                        }
                        if replaced {
                            break;
                        }
                    }
                }
            }

            _ => (),
        }
        simplified_formula
    }

    pub(crate) fn eliminate_redundant_quantifiers(formula: Formula) -> Formula {
        match formula.clone().unbox() {
            // Remove redundant existentials
            // e.g. exists Z$g (Z$g = X$g and F(Z$g)) => F(X$g)
            UnboxedFormula::QuantifiedFormula {
                quantification:
                    Quantification {
                        quantifier: Quantifier::Exists,
                        mut variables,
                    },
                formula: f,
            } => match f.clone().unbox() {
                UnboxedFormula::BinaryFormula {
                    connective: BinaryConnective::Conjunction,
                    ..
                } => {
                    let simplification_result =
                        simplify_conjunction_tree_with_equality(f, variables.clone());
                    match simplification_result.1 {
                        Some(sub_pair) => {
                            variables.retain(|v| v != &sub_pair.0);
                            Formula::QuantifiedFormula {
                                quantification: Quantification {
                                    quantifier: Quantifier::Exists,
                                    variables,
                                },
                                formula: simplification_result.0.into(),
                            }
                        }
                        None => formula,
                    }
                }
                _ => formula,
            },

            // A universally quantified implication can sometimes be simplified
            // e.g. forall X1 .. Xj .. Xn  (F1 and .. Fi .. and Fm -> G), where Fi is Xj=t, and Xj doesn’t occur in t, and free variables occurring in t are not bound by quantifiers in F1, F2, ..
            // becomes forall X1 .. Xn  (F1 and .. and Fm -> G)
            UnboxedFormula::QuantifiedFormula {
                quantification:
                    Quantification {
                        quantifier: Quantifier::Forall,
                        mut variables,
                    },
                formula:
                    Formula::BinaryFormula {
                        connective: BinaryConnective::Implication,
                        lhs,
                        rhs,
                    },
            } => match lhs.clone().unbox() {
                UnboxedFormula::BinaryFormula {
                    connective: BinaryConnective::Conjunction,
                    ..
                } => {
                    let mut f = formula;
                    let lhs_simplify =
                        simplify_conjunction_tree_with_equality(*lhs, variables.clone());
                    match lhs_simplify.1 {
                        Some(sub_pair) => {
                            if !rhs.clone().unsafe_substitution(&sub_pair.0, &sub_pair.1) {
                                variables.retain(|v| v != &sub_pair.0);
                                f = Formula::QuantifiedFormula {
                                    quantification: Quantification {
                                        quantifier: Quantifier::Forall,
                                        variables,
                                    },
                                    formula: Formula::BinaryFormula {
                                        connective: BinaryConnective::Implication,
                                        lhs: lhs_simplify.0.into(),
                                        rhs: rhs.substitute(sub_pair.0, sub_pair.1).into(),
                                    }
                                    .into(),
                                };
                            }
                            f
                        }
                        None => f,
                    }
                }

                _ => formula,
            },

            _ => formula,
        }
    }

    pub(crate) fn extend_quantifier_scope(formula: Formula) -> Formula {
        match formula.clone().unbox() {
            // Bring a conjunctive or disjunctive term into the scope of a quantifer
            // e.g. exists X ( F(X) ) & G => exists X ( F(X) & G )
            // where X does not occur free in G
            UnboxedFormula::BinaryFormula {
                connective,
                lhs:
                    Formula::QuantifiedFormula {
                        quantification:
                            Quantification {
                                quantifier,
                                variables,
                            },
                        formula: f,
                    },
                rhs,
            } => match connective {
                BinaryConnective::Conjunction | BinaryConnective::Disjunction => {
                    let mut collision = false;
                    for var in variables.iter() {
                        if rhs.free_variables().contains(var) {
                            collision = true;
                            break;
                        }
                    }

                    match collision {
                        true => formula,
                        false => Formula::QuantifiedFormula {
                            quantification: Quantification {
                                quantifier,
                                variables,
                            },
                            formula: Formula::BinaryFormula {
                                connective,
                                lhs: f,
                                rhs: rhs.into(),
                            }
                            .into(),
                        },
                    }
                }
                _ => formula,
            },

            UnboxedFormula::BinaryFormula {
                connective,
                lhs,
                rhs:
                    Formula::QuantifiedFormula {
                        quantification:
                            Quantification {
                                quantifier,
                                variables,
                            },
                        formula: f,
                    },
            } => match connective {
                BinaryConnective::Conjunction | BinaryConnective::Disjunction => {
                    let mut collision = false;
                    for var in variables.iter() {
                        if lhs.free_variables().contains(var) {
                            collision = true;
                            break;
                        }
                    }

                    match collision {
                        true => formula,
                        false => Formula::QuantifiedFormula {
                            quantification: Quantification {
                                quantifier,
                                variables,
                            },
                            formula: Formula::BinaryFormula {
                                connective,
                                lhs: lhs.into(),
                                rhs: f,
                            }
                            .into(),
                        },
                    }
                }
                _ => formula,
            },

            x => x.rebox(),
        }
    }

    pub(crate) fn simplify_transitive_equality(formula: Formula) -> Formula {
        match formula.clone().unbox() {
            // When X is a subsort of Y (or sort(X) = sort(Y)) and t is a term:
            // exists X Y (X = t and Y = t and F)
            // =>
            // exists X Y (X = t and F(X))
            // Replace Y with X within F
            // Keep Y in the quantification just in case you have
            // the corner case Y = Y & Y= Y & F(Y)
            // Remove Orphaned Variables can handle Y later
            UnboxedFormula::QuantifiedFormula {
                quantification:
                    Quantification {
                        quantifier: Quantifier::Exists,
                        variables,
                    },
                formula: f,
            } => match f.clone().unbox() {
                UnboxedFormula::BinaryFormula {
                    connective: BinaryConnective::Conjunction,
                    ..
                } => {
                    let mut simplified = formula.clone();
                    let mut simplify = false;
                    let conjunctive_terms = conjoin_invert(f.clone());
                    let mut ct_copy = conjunctive_terms.clone();
                    for (i, ct1) in conjunctive_terms.iter().enumerate() {
                        // Search for an equality formula
                        if let Formula::AtomicFormula(AtomicFormula::Comparison(c1)) = ct1 {
                            if equality_comparison(c1) {
                                for (j, ct2) in conjunctive_terms.iter().enumerate() {
                                    // Search for a second equality formula
                                    if let Formula::AtomicFormula(AtomicFormula::Comparison(c2)) =
                                        ct2
                                    {
                                        if equality_comparison(c2) && i != j {
                                            if let Some((keep_var, drop_var, drop_term)) =
                                                transitive_equality(
                                                    c1.clone(),
                                                    c2.clone(),
                                                    variables.clone(),
                                                )
                                            {
                                                //variables.retain(|x| x != &drop_var);
                                                ct_copy.retain(|t| {
                                                    t != &Formula::AtomicFormula(
                                                        AtomicFormula::Comparison(
                                                            drop_term.clone(),
                                                        ),
                                                    )
                                                });
                                                let keep = match keep_var.sort {
                                                    Sort::General => {
                                                        GeneralTerm::Variable(keep_var.name)
                                                    }
                                                    Sort::Integer => GeneralTerm::IntegerTerm(
                                                        IntegerTerm::Variable(keep_var.name),
                                                    ),
                                                    Sort::Symbol => GeneralTerm::SymbolicTerm(
                                                        SymbolicTerm::Variable(keep_var.name),
                                                    ),
                                                };
                                                let inner = Formula::conjoin(ct_copy.clone())
                                                    .substitute(drop_var, keep);
                                                simplified = Formula::QuantifiedFormula {
                                                    quantification: Quantification {
                                                        quantifier: Quantifier::Exists,
                                                        variables: variables.clone(),
                                                    },
                                                    formula: inner.into(),
                                                };
                                                simplify = true;
                                            }
                                        }
                                    }
                                    if simplify {
                                        break;
                                    }
                                }
                            }
                        }
                        if simplify {
                            break;
                        }
                    }
                    simplified
                }

                _ => formula,
            },

            x => x.rebox(),
        }
    }

    #[cfg(test)]
    mod tests {
        use crate::{convenience::apply::Apply as _, syntax_tree::fol::Formula};

        use super::{
            extend_quantifier_scope, restrict_quantifier_domain, eliminate_redundant_quantifiers,
            simplify_transitive_equality,
        };

        #[test]
        fn test_restrict_quantifiers() {
            for (src, target) in [
                (
                    "exists Z Z1 ( exists I$i J$i ( Z = J$i and q(I$i, J$i) ) and Z = Z1 )",
                    "exists Z1 J1$i ( exists I$i J$i ( J1$i = J$i and q(I$i, J$i) ) and J1$i = Z1 )",
                ),
                (
                    "exists Z Z1 ( exists I$i J$i ( q(I$i, J$i) and Z = J$i) and Z = Z1 )",
                    "exists Z1 J1$i ( exists I$i J$i ( q(I$i, J$i) and J1$i = J$i) and J1$i = Z1 )",
                ),
                (
                    "exists Z Z1 ( Z = Z1 and exists I$i J$i ( q(I$i, J$i) and Z = J$i) )",
                    "exists Z1 J1$i ( J1$i = Z1 and exists I$i J$i ( q(I$i, J$i) and J1$i = J$i) )",
                ),
                (
                    "exists Z Z1 ( Z = Z1 and exists I$i J$i ( q(I$i, J$i) and Z = J$i and 3 > 2) and 1 < 5 )",
                    "exists Z1 J1$i ( J1$i = Z1 and exists I$i J$i ( q(I$i, J$i) and J1$i = J$i and 3 > 2) and 1 < 5 )",
                ),
                (
                    "forall X Y ( exists Z I$i (p(X) and p(Z) and Y = I$i) -> q(X) )",
                    "forall X I1$i ( exists Z I$i (p(X) and p(Z) and I1$i = I$i) -> q(X) )",
                ),
                (
                    "forall X Y ( exists Z I$i (p(X) and p(Z) and Y = I$i) -> q(Y) )",
                    "forall X Y ( exists Z I$i (p(X) and p(Z) and Y = I$i) -> q(Y) )",
                ),
                (
                    "forall X Y ( exists I$i J$i (Y = J$i and p(I$i, J$i) and I$i = X) -> q(Z) )",
                    "forall X J1$i ( exists I$i J$i (J1$i = J$i and p(I$i, J$i) and I$i = X) -> q(Z) )",
                ),
                (
                    "forall X Y ( exists Z I$i (p(X,Z) or Y = I$i) -> q(X) )",
                    "forall X Y ( exists Z I$i (p(X,Z) or Y = I$i) -> q(X) )",
                ),
                (
                    "forall X Y ( exists Z I$i (p(X,Z) and I$i = X) -> exists A X (q(A,X)) )",
                    "forall Y I1$i ( exists Z I$i (p(I1$i,Z) and I$i = I1$i) -> exists A X (q(A,X)) )",
                ),
            ] {
                let src = restrict_quantifier_domain(src.parse().unwrap());
                let target = target.parse().unwrap();
                assert_eq!(src, target, "{src} != {target}")
            }
        }

        #[test]
        fn test_extend_quantification_scope() {
            for (src, target) in [
                (
                    "exists X (q(X) and 1 < 3) and p(Z)",
                    "exists X (q(X) and 1 < 3 and p(Z))",
                ),
                (
                    "exists X (q(X) and 1 < 3) and p(X)",
                    "exists X (q(X) and 1 < 3) and p(X)",
                ),
                (
                    "forall Z X (q(X) and 1 < Z) or p(Y,Z$)",
                    "forall Z X (q(X) and 1 < Z or p(Y,Z$))",
                ),
                (
                    "p(Z) and exists X (q(X) and 1 < 3)",
                    "exists X (p(Z) and (q(X) and 1 < 3))",
                ),
            ] {
                let result = extend_quantifier_scope(src.parse().unwrap());
                let target = target.parse().unwrap();
                assert_eq!(result, target, "{result} != {target}")
            }
        }

        #[test]
        fn test_simplify_transitive_equality() {
            for (src, target) in [
            (
                "exists X Y Z ( X = 5 and Y = 5 and not p(X,Y))",
                "exists X Y Z ( X = 5 and not p(X,X))",
            ),
            (
                "forall V1 (orphan(V1) <-> exists Y Z (V1 = V1 and (V1 = V1 and living(V1) and (Y = Y and V1 = V1 and father(Y, V1)) and (Z = Z and V1 = V1 and mother(Z, V1)) and (Y = Y and not living(Y)) and (Z = Z and not living(Z)))))",
                "f",
            ),
            ] {
                let src: Formula = src.parse().unwrap();
                let simplified = src.apply(&mut simplify_transitive_equality);
                let target = target.parse().unwrap();
                assert_eq!(simplified, target, "{simplified} != {target}")
            }
        }
    }

    #[test]
    fn test_eliminate_redundant_quantifiers() {
        for (src, target) in [
            ("exists X ( X = Z and not q(X) )", "not q(Z)"),
            (
                "exists Y ( Y = X and forall V (p(Y,V) -> q(X)) )",
                "forall V (p(X,V) -> q(X))",
            ),
            (
                "exists Z Z1 ( Z = I and (exists K$i (K$i = I) and Z = Z1) )",
                "exists Z1 ( exists K$i (K$i = I) and I = Z1)",
            ),
            (
                "forall X V (p(X) and X = V -> q(V))",
                "forall V (p(V) -> q(V))",
            ),
        ] {
            let src = crate::simplifying::fol::intuitionistic::remove_empty_quantifications(
                eliminate_redundant_quantifiers(src.parse().unwrap()),
            );
            let target = target.parse().unwrap();
            assert_eq!(src, target, "{src} != {target}")
        }
    }
}
