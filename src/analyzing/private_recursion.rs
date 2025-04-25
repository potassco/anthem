use {
    crate::syntax_tree::asp::{
        Predicate,
        mini_gringo::{Head, Program},
    },
    indexmap::IndexSet,
    petgraph::{algo::is_cyclic_directed, graph::DiGraph},
    std::collections::HashMap,
};

pub trait PrivateRecursion {
    fn has_private_recursion(&self, private_predicates: &IndexSet<Predicate>) -> bool;
}

impl PrivateRecursion for Program {
    fn has_private_recursion(&self, private_predicates: &IndexSet<Predicate>) -> bool {
        for rule in &self.rules {
            match rule.head {
                Head::Choice(ref a) => {
                    if private_predicates.contains(&a.predicate()) {
                        return true;
                    }
                }
                Head::Basic(_) | Head::Falsity => (),
            }
        }

        let mut dependency_graph = DiGraph::<(), ()>::new();
        let mut mapping = HashMap::new();

        for predicate in self.predicates() {
            if private_predicates.contains(&predicate) {
                let node = dependency_graph.add_node(());
                mapping.insert(predicate, node);
            }
        }

        for rule in &self.rules {
            if let Some(head_predicate) = rule.head.predicate() {
                if private_predicates.contains(&head_predicate) {
                    for body_predicate in rule.body.predicates() {
                        if private_predicates.contains(&body_predicate) {
                            dependency_graph.update_edge(
                                mapping[&head_predicate],
                                mapping[&body_predicate],
                                (),
                            );
                        }
                    }
                }
            }
        }

        is_cyclic_directed(&dependency_graph)
    }
}

#[cfg(test)]
mod tests {
    use {
        crate::{
            analyzing::private_recursion::PrivateRecursion,
            syntax_tree::asp::{Predicate, mini_gringo::Program},
        },
        indexmap::IndexSet,
        std::str::FromStr,
    };

    #[test]
    fn test_private_recursion() {
        let private_predicates: IndexSet<Predicate> = IndexSet::from_iter(
            ["a/0", "b/0", "p/1"]
                .into_iter()
                .map(|p| p.parse().unwrap()),
        );

        for program in ["a :- not c. c :- not a.", "a :- p(1). p(X) :- q(X)."] {
            assert!(
                !Program::from_str(program)
                    .unwrap()
                    .has_private_recursion(&private_predicates)
            )
        }

        for program in [
            "{a}.",
            "a :- not a.",
            "a :- not not a.",
            "a :- not b. b :- not a.",
            "{p(X)} :- not not p(X). b :- a.",
        ] {
            assert!(
                Program::from_str(program)
                    .unwrap()
                    .has_private_recursion(&private_predicates)
            )
        }
    }
}
