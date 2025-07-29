use {
    crate::syntax_tree::{
        asp::{Body, Head, Program, Rule},
        fol::{self, UserGuide},
    },
    petgraph::{algo::bellman_ford::find_negative_cycle, graph::DiGraph},
    std::collections::HashMap,
};

pub trait Stratification {
    fn is_stratified(&self) -> bool;
}

impl Stratification for Program {
    fn is_stratified(&self) -> bool {
        let mut dependency_graph = DiGraph::<(), f32>::new();
        let mut mapping = HashMap::new();

        // add all predicate to the dependency graph
        for predicate in self.predicates() {
            let node = dependency_graph.add_node(());
            mapping.insert(predicate, node);
        }

        // add rules as edges to the dependency graph
        for rule in &self.rules {
            match rule {
                // a program containing choices or constraints is not stratified
                Rule {
                    head: Head::Choice(_) | Head::Falsity,
                    body: _,
                } => return false,

                Rule {
                    head: Head::Basic(a),
                    body,
                } => {
                    // for basic rules we add edges from the head predicate to the body predicates
                    // for negative body predicates we want to have an edge with negative weight
                    // for positive body predicates an edge with weight zero
                    // but we need to take care to not overwrite negative edges with a positive edge
                    // (technically we should have both positive and negative edges at the same time,
                    // but it is sufficient to "discard" positive edges once we have a negative edge
                    // as we are only interested in stratification and not e.g. tightness)
                    // we do so by always adding the new weight to the current weight of the edge
                    // if an edge does not yet exist we set the current weight to zero

                    let head_predicate = a.predicate();
                    let negative_body_predicates = body.negative_predicates();
                    for body_predicate in body.predicates() {
                        let source = mapping[&head_predicate];
                        let target = mapping[&body_predicate];

                        // get current weight of edge between source and target
                        let current_weight = dependency_graph
                            .find_edge(source, target)
                            .map(|edge| dependency_graph[edge])
                            // if no edge exists then set to 0.0
                            .unwrap_or(0.0);

                        // determine the newly added weight
                        let new_weight = {
                            if negative_body_predicates.contains(&body_predicate) {
                                -1.0
                            } else {
                                0.0
                            }
                        };

                        dependency_graph.update_edge(source, target, current_weight + new_weight);
                    }
                }
            }
        }

        // for each node check if there is a negative cycle starting at that node
        // i.e. a cycle going through at least one negative edge
        for node in dependency_graph.node_indices() {
            if find_negative_cycle(&dependency_graph, node).is_some() {
                return false;
            }
        }

        true
    }
}

pub trait WeakStratification {
    fn is_weakly_stratified(&self) -> bool;
}

impl WeakStratification for Program {
    fn is_weakly_stratified(&self) -> bool {
        // filter out all constraints
        let filtered_rules = self
            .rules
            .clone()
            .into_iter()
            .filter(|rule| !rule.is_constraint())
            .collect();

        Program {
            rules: filtered_rules,
        }
        .is_stratified()
    }
}

trait PrivatePart {
    fn private_part(&self, user_guide: &UserGuide) -> Self;
}

impl PrivatePart for Program {
    fn private_part(&self, user_guide: &UserGuide) -> Self {
        fn is_private_head(head: &Head, user_guide: &UserGuide) -> bool {
            let head_predicate = head.predicate();
            if let Some(head_predicate) = head_predicate {
                // for basic and choice heads the predicate needs to be private
                !user_guide
                    .public_predicates()
                    .contains(&fol::Predicate::from(head_predicate))
            } else {
                // constraint heads are always private
                true
            }
        }

        // check if a body is private
        fn is_private_body(body: &Body, user_guide: &UserGuide) -> bool {
            for predicate in body.predicates() {
                if !user_guide
                    .public_predicates()
                    .contains(&fol::Predicate::from(predicate))
                {
                    // a body is private if it contains some private predicate
                    return true;
                }
            }

            false
        }

        // check if the rule is private
        fn is_private_rule(rule: &Rule, user_guide: &UserGuide) -> bool {
            match rule {
                // for choices we just need to check whether the head is private
                Rule {
                    head: head @ Head::Choice(_),
                    body: _,
                } => is_private_head(head, user_guide),

                // for constraints we just need to check whether the body is private
                Rule {
                    head: Head::Falsity,
                    body,
                } => is_private_body(body, user_guide),

                // for basic rules both the head and the body need to be private
                Rule {
                    head: head @ Head::Basic(_),
                    body,
                } => is_private_head(head, user_guide) && is_private_body(body, user_guide),
            }
        }

        // computed the private part of the program
        let private_rules: Vec<Rule> = self
            .rules
            .clone()
            .into_iter()
            .filter(|r| is_private_rule(r, user_guide))
            .collect();

        Program {
            rules: private_rules,
        }
    }
}

pub trait PrivateStratification {
    fn is_private_stratified(&self, user_guide: &UserGuide) -> bool;
}

impl PrivateStratification for Program {
    fn is_private_stratified(&self, user_guide: &UserGuide) -> bool {
        // check stratification for the private part of the program
        self.private_part(user_guide).is_stratified()
    }
}

pub trait PrivateWeakStratification {
    fn is_private_weakly_stratified(&self, user_guide: &UserGuide) -> bool;
}

impl PrivateWeakStratification for Program {
    fn is_private_weakly_stratified(&self, user_guide: &UserGuide) -> bool {
        self.private_part(user_guide).is_weakly_stratified()
    }
}

#[cfg(test)]
mod tests {
    use {
        super::{
            PrivateStratification, PrivateWeakStratification, Stratification, WeakStratification,
        },
        crate::syntax_tree::{asp::Program, fol::UserGuide},
        std::str::FromStr,
    };

    #[test]
    fn test_stratification() {
        for program in ["a.", "a :- a.", "a :- b. b :- a."] {
            assert!(
                Program::from_str(program).unwrap().is_stratified(),
                "assertion failed:\n program should be stratified:\n {program}"
            );
        }

        for program in [
            "{ a }.",
            "a :- not a.",
            "a :- not b. b :- not a.",
            "p(X) :- not q(X). q(X) :- p(X).",
            "q(X) :- p(X). p(X) :- not q(X).",
            "p :- q, not r. p :- r. r :- p.",
            ":- a.",
        ] {
            assert!(
                !Program::from_str(program).unwrap().is_stratified(),
                "assertion failed:\n program should not be stratified:\n {program}"
            );
        }
    }

    #[test]
    fn test_weak_stratification() {
        for program in ["a.", "a :- a.", "a :- b. b :- a.", ":- a."] {
            assert!(
                Program::from_str(program).unwrap().is_weakly_stratified(),
                "assertion failed:\n program should be weakly stratified:\n {program}"
            );
        }

        for program in [
            "{ a }.",
            "a :- not a.",
            "a :- not b. b :- not a.",
            "p(X) :- not q(X). q(X) :- p(X).",
            "q(X) :- p(X). p(X) :- not q(X).",
            "p :- q, not r. p :- r. r :- p.",
        ] {
            assert!(
                !Program::from_str(program).unwrap().is_weakly_stratified(),
                "assertion failed:\n program should not be weakly stratified:\n {program}"
            );
        }
    }

    #[test]
    fn test_private_stratification() {
        let user_guide = &UserGuide::from_str("input: p/0. output: q/0.").unwrap();

        for program in [
            "{ a }.",
            "a :- not b. b :- not a.",
            ":- a.",
            "a :- b. b :- not a.",
            "b :- not a. a :- b.",
        ] {
            assert!(
                !Program::from_str(program)
                    .unwrap()
                    .is_private_stratified(user_guide),
                "assertion failed:\n program should not be privately stratified:]n {program}"
            );
        }

        for program in [
            "{ p }.",
            "p :- not q. q :- not p.",
            "p :- q. q :- p.",
            "a :- b. b :- a.",
            ":- p.",
            "p :- a. a :- p.",
            "p :- not a. a :- not p.",
        ] {
            assert!(
                Program::from_str(program)
                    .unwrap()
                    .is_private_stratified(user_guide),
                "assertion failed:\n program should be privately stratified:\n {program}"
            );
        }
    }

    #[test]
    fn test_private_weak_stratification() {
        let user_guide = &UserGuide::from_str("input: p/0. output: q/0.").unwrap();

        for program in [
            "{ a }.",
            "a :- not b. b :- not a.",
            "a :- b. b :- not a.",
            "b :- not a. a :- b.",
        ] {
            assert!(
                !Program::from_str(program)
                    .unwrap()
                    .is_private_weakly_stratified(user_guide),
                "assertion failed:\n program should not be private weakly stratified:]n {program}"
            );
        }

        for program in [
            "{ p }.",
            "p :- not q. q :- not p.",
            "p :- q. q :- p.",
            "a :- b. b :- a.",
            ":- p.",
            "p :- a. a :- p.",
            "p :- not a. a :- not p.",
            ":- a.",
        ] {
            assert!(
                Program::from_str(program)
                    .unwrap()
                    .is_private_weakly_stratified(user_guide),
                "assertion failed:\n program should be private weakly stratified:\n {program}"
            );
        }
    }
}
