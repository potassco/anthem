use {
    crate::syntax_tree::asp::mini_gringo::Program,
    petgraph::{algo::is_cyclic_directed, graph::DiGraph},
    std::collections::HashMap,
};

pub trait Tightness {
    fn is_tight(&self) -> bool;
}

impl Tightness for Program {
    fn is_tight(&self) -> bool {
        let mut dependency_graph = DiGraph::<(), ()>::new();
        let mut mapping = HashMap::new();

        for predicate in self.predicates() {
            let node = dependency_graph.add_node(());
            mapping.insert(predicate, node);
        }

        for rule in &self.rules {
            if let Some(head_predicate) = rule.head.predicate() {
                for positive_body_predicate in rule.body.positive_predicates() {
                    dependency_graph.update_edge(
                        mapping[&head_predicate],
                        mapping[&positive_body_predicate],
                        (),
                    );
                }
            }
        }

        !is_cyclic_directed(&dependency_graph)
    }
}

#[cfg(test)]
mod tests {
    use {super::Tightness, crate::syntax_tree::asp::mini_gringo::Program, std::str::FromStr};

    #[test]
    fn test_tightness() {
        for program in [
            "a.",
            "a :- not a.",
            "a :- not b. b :- not a.",
            "p(a) :- p.",
            "p(X) :- not q(X). q(X) :- p(X).",
        ] {
            assert!(Program::from_str(program).unwrap().is_tight())
        }

        for program in [
            "a :- a.",
            "a :- b. b :- a.",
            "p :- q, not r. p :- r. r :- p.",
        ] {
            assert!(!Program::from_str(program).unwrap().is_tight())
        }
    }
}
