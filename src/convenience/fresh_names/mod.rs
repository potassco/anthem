use {
    crate::syntax_tree::{asp::mini_gringo, fol::sigma_0 as fol},
    indexmap::IndexSet,
};

pub(crate) fn choose_fresh_names(
    variant: &str,
    n: usize,
    is_taken: impl Fn(&str) -> bool,
) -> Vec<String> {
    std::iter::once(variant.to_string())
        .chain((1..).map(|i| format!("{variant}{i}")))
        .filter(|c| !is_taken(c))
        .take(n)
        .collect()
}

pub(crate) trait FreshVariables {
    /// Select n variable names using `variant` disjoint from any variables in `self`
    fn choose_fresh_variables(&self, variant: &str, n: usize) -> Vec<String>;

    /// Select a variable name using `variant` disjoint from any variables in `self`
    fn choose_fresh_variable(&self, variant: &str) -> String {
        self.choose_fresh_variables(variant, 1).pop().unwrap()
    }
}

impl FreshVariables for IndexSet<fol::Variable> {
    fn choose_fresh_variables(&self, variant: &str, n: usize) -> Vec<String> {
        let taken_var_names: IndexSet<&str> = self.iter().map(|v| v.name.as_str()).collect();
        choose_fresh_names(variant, n, |c| taken_var_names.contains(c))
    }
}

impl FreshVariables for IndexSet<mini_gringo::Variable> {
    fn choose_fresh_variables(&self, variant: &str, n: usize) -> Vec<String> {
        let taken_var_names: IndexSet<&str> = self.iter().map(|v| v.0.as_str()).collect();
        choose_fresh_names(variant, n, |c| taken_var_names.contains(c))
    }
}

impl FreshVariables for mini_gringo::Program {
    // Choose sequence of variants numbered above the highest one taken in the program,
    // e.g. if the program contains V2, start selection from V3,
    //      even if the program does not contain V1
    fn choose_fresh_variables(&self, variant: &str, n: usize) -> Vec<String> {
        let max_taken_var = self
            .variables()
            .iter()
            .filter_map(|v| v.0.strip_prefix(variant))
            .map(|suffix| suffix.parse::<usize>().unwrap_or(0))
            .max()
            .unwrap_or(0);

        ((max_taken_var + 1)..(max_taken_var + n + 1))
            .map(|i| format!("{variant}{i}"))
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use indexmap::IndexSet;

    use crate::{
        convenience::fresh_names::FreshVariables,
        syntax_tree::{asp, fol::sigma_0 as fol},
    };

    #[test]
    fn test_choose_variables_indexset_fol() {
        let taken_vars: IndexSet<fol::Variable> =
            IndexSet::from_iter(["I", "J", "J1", "V1"].iter().map(|name| fol::Variable {
                name: name.to_string(),
                sort: fol::Sort::General,
            }));

        assert_eq!(taken_vars.choose_fresh_variable("I"), "I1".to_string());
        assert_eq!(taken_vars.choose_fresh_variable("J"), "J2".to_string());
        assert_eq!(taken_vars.choose_fresh_variable("V"), "V".to_string());
    }

    #[test]
    fn test_choose_variables_program() {
        for (program, arity, variables) in [
            ("p(X) :- q(X,Y).", 1, Vec::from_iter(["V1"])),
            ("p(X,V1) :- q(X,V3).", 2, Vec::from_iter(["V4", "V5"])),
        ] {
            let program: asp::mini_gringo::Program = program.parse().unwrap();
            let chosen = program.choose_fresh_variables("V", arity);
            let target: Vec<String> = variables.iter().map(|v| v.to_string()).collect();
            assert_eq!(chosen, target);
        }
    }
}
