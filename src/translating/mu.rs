use crate::{
    syntax_tree::{fol, mini_gringo},
    translating::{natural, tau_star},
};

pub fn mu(p: mini_gringo::Program) -> fol::Theory {
    let mut formulas: Vec<fol::Formula> = vec![];
    let globals = tau_star::choose_fresh_global_variables(&p);

    for r in p.rules {
        match natural::natural_rule(&r) {
            Some(f) => formulas.push(f),
            None => formulas.push(tau_star::tau_star_rule(&r, &globals)),
        }
    }

    fol::Theory { formulas }
}

#[cfg(test)]
mod tests {
    use {super::mu, crate::syntax_tree::fol};

    #[test]
    fn test_mu() {
        for (source, target) in [
            (
                "p(X) :- q(X). q(4/2).",
                "forall X (q(X) -> p(X)). forall V1 (exists I$i J$i Q$i R$i (I$i = J$i * Q$i + R$i and (I$i = 4 and J$i = 2) and (J$i != 0 and R$i >= 0 and R$i < J$i) and V1 = Q$i) and #true -> q(V1)).",
            ),
            (
                "p(X) :- q(1..5), a(X). q(1..3) :- p(X).",
                "forall V1 X (V1 = X and (exists Z (exists I$i J$i K$i (I$i = 1 and J$i = 5 and Z = K$i and I$i <= K$i <= J$i) and q(Z)) and exists Z (Z = X and a(Z))) -> p(V1)).\nforall X (p(X) -> forall N0$i (1 <= N0$i <= 3 -> q(N0$i))).",
            ),
        ] {
            let rule = source.parse().unwrap();
            let mu: fol::Theory = mu(rule);
            let mu_string = mu.to_string();
            let target_theory: fol::Theory = target.parse().unwrap();
            let target = target_theory.to_string();
            assert_eq!(
                mu, target_theory,
                "assertion `mu(source) == target` failed:\n mu:\n{mu_string:?}\n target:\n{target:?}",
            );
        }
    }
}
