pub mod apply;
pub mod compose;
pub mod unbox;
pub mod with_warnings;

/// Choose `arity` variable names by incrementing `variant`, disjoint from `taken_vars`
pub(crate) fn choose_fresh_variable_names(
    taken_vars: Vec<String>,
    variant: &str,
    arity: usize,
) -> Vec<String> {
    if arity < 1 {
        return Vec::new();
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
