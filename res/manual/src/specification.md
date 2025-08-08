# Specification (.spec)
The verification of external equivalence compares a mini-gringo program to a specification.
A specification can be written as another mini-gringo program `Π` or as a control language specification `S`.

### Logic Program Specifications
If the specification is a program `Π`, then `Π` must not contain input symbols in any rule heads.
Additionally, `Π` must be tight and free of private recursion.
This is because the formula representation of `Π` will be obtained via tau-star and completion (`COMP[τ*Π1]`).
The completed definitions of private predicates from this theory will be treated as assumptions in the `forward` and `backward` directions of the proof.
The remaining formulas from `COMP[τ*Π1]` will be treated analogously to formulas with the `spec(universal)` annotation (as described below).


### Control Language Specifications
If the specification is `S`, it consists of annotated formulas of three types: assumptions, definitions and specs.
All formulas must be closed.

#### Definitions
For convenience, a specification may contain a sequence of definitions (similarly to proof outlines).
These formulas introduce fresh predicates on the LHS of an equivalence.

A sequence is *valid for use within assumptions* if it satisfies that
1. the RHS of the first definition contains only input predicates from the user guide,
2. the RHS of subsequent definitions contains only input predicates and previously defined predicates, and
3. the LHS of every definition contains a fresh predicate.
A fresh predicate does not occur in the list of input or output predicates, and has not been previously defined.

We consider a predicate to be valid for use within assumptions when it is the last definition in a sequence that is valid for use within assumptions.

Using defined predicates in specs is less restrictive insofar as that output predicates may also be used within the RHS of definitions.
Thus, a sequence is *valid for use within specs* if it satisfies that
1. the RHS of the first definition contains only public predicates,
2. the RHS of subsequent definitions contains only public predicates and previously defined predicates, and
3. the LHS of every definition contains a fresh predicate.

Similarly, a predicate to be valid for use within specs when it is the last definition in a sequence that is valid for use within specs.

The following specification from the `twin primes` problem contains an example of a definition that is valid for use within assumptions (and thus also for use within specs):

```
definition: forall X (prime(X) <-> 2 <= X <= n and not exists D$i M$i (1 < D$i < X and M$i*D$i = X)).
spec: forall X Y (twins(X,Y) <-> prime(X) and prime(Y) and X + 2 = Y).
```

#### Assumptions
Atoms within assumptions may be formed from any predicate symbols that are valid for use within assumptions.
The following assumption comes from a specification defining the expected behavior of a Graph Coloring program:

```
    assumption: forall X Y (edge(X,Y) -> vertex(X) and vertex(Y)).
```

#### Specs
Atoms within specs may be formed from any predicate symbols that are valid for use within specs.
Specs with the `universal` annotation are treated as axioms in the `forward` direction of the proof, and as conjectures in the `backward` direction.
A spec with a `forward` annotation is an axiom in the `forward` direction and ignored in the backward direction.
Similarly, a spec with a `backward` annotation is a conjecture in the `backward` direction and ignored in the forward direction.

The following set of universal specs complete the specification for the Graph Coloring problem introduced earlier:

```
    spec: forall X Z (color(X,Z) -> vertex(X) and color(Z)).
    spec: forall X (vertex(X) -> exists Z color(X,Z)).
    spec: forall X Z1 Z2 (color(X,Z1) and color(X,Z2) -> Z1 = Z2).
    spec: not exists X Y Z (edge(X,Y) and color(X,Z) and color(Y,Z)).
```
