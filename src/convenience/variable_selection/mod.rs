use {
    crate::syntax_tree::{asp::mini_gringo, fol::sigma_0 as fol},
    indexmap::IndexSet,
    regex::Regex,
};

fn sequence(start: usize, prefix: &String) -> impl Iterator<Item = String> {
    (start..).map(move |i| format!("{}{}", prefix, i))
}

pub(crate) trait VariableSelection {
    /// Select a variable name using `variant` disjoint from any variables in `self`
    fn choose_fresh_variable(&self, variant: &str) -> String;

    /// Select n variable names using `variant` disjoint from any variables in `self`
    fn choose_fresh_variables(&self, variant: &str, n: usize) -> Vec<String>;
}

impl VariableSelection for IndexSet<fol::Variable> {
    fn choose_fresh_variable(&self, variant: &str) -> String {
        let mut taken_var_names = IndexSet::new();
        for var in self.iter() {
            taken_var_names.insert(var.name.clone());
        }

        if !taken_var_names.contains(variant) {
            return variant.to_string();
        }

        let prefix = variant.to_string();
        sequence(1, &prefix)
            .find(|candidate| !taken_var_names.contains(candidate))
            .unwrap()
    }

    fn choose_fresh_variables(&self, variant: &str, n: usize) -> Vec<String> {
        let mut taken_var_names = IndexSet::new();
        for var in self.iter() {
            taken_var_names.insert(var.name.clone());
        }

        let mut selected_variables = Vec::new();

        if n < 1 {
            return selected_variables;
        }

        if !taken_var_names.contains(variant) {
            selected_variables.push(variant.to_string());
        }

        let mut i = 1;
        let prefix = variant.to_string();
        while selected_variables.len() < n {
            let fresh_var = sequence(i, &prefix)
                .find(|candidate| {
                    !taken_var_names.contains(candidate) && !selected_variables.contains(candidate)
                })
                .unwrap();
            selected_variables.push(fresh_var);
            i += 1;
        }

        selected_variables
    }
}

impl VariableSelection for IndexSet<mini_gringo::Variable> {
    fn choose_fresh_variable(&self, variant: &str) -> String {
        let prefix = variant.to_string();
        sequence(0, &prefix)
            .find(|candidate| !self.contains(&mini_gringo::Variable(candidate.to_string())))
            .unwrap()
    }

    fn choose_fresh_variables(&self, variant: &str, n: usize) -> Vec<String> {
        let mut selected_variables = Vec::new();
        let mut taken_variables = self.clone();
        for _ in 0..n {
            let fresh_var_name = taken_variables.choose_fresh_variable(variant);
            taken_variables.insert(mini_gringo::Variable(fresh_var_name.clone()));
            selected_variables.push(fresh_var_name);
        }
        selected_variables
    }
}

impl VariableSelection for mini_gringo::Program {
    fn choose_fresh_variable(&self, variant: &str) -> String {
        self.variables().choose_fresh_variable(variant)
    }

    // Choose the first available sequence of variants (alphabetically first)
    // e.g. if the program contains V2, start selection from V3,...
    fn choose_fresh_variables(&self, variant: &str, n: usize) -> Vec<String> {
        let mut max_taken_var = 0;
        let re = Regex::new(&format!(r"^{variant}(?<number>[0-9]*)$")).unwrap();
        for var in self.variables() {
            if let Some(caps) = re.captures(&var.0) {
                let taken: usize = (caps["number"]).parse().unwrap_or(0);
                if taken > max_taken_var {
                    max_taken_var = taken;
                }
            }
        }
        ((max_taken_var + 1)..(max_taken_var + n + 1))
            .map(|i| format!("{variant}{i}"))
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use indexmap::IndexSet;

    use crate::{
        convenience::variable_selection::VariableSelection,
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
