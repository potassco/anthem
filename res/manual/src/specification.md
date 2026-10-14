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

A sequence of definitions is *valid* if it satisfies that
1. the RHS of the first definition contains only input predicates from the user guide,
2. the RHS of subsequent definitions contains only input predicates and previously defined predicates, and
3. the LHS of every definition contains a fresh predicate.
A fresh predicate does not occur in the list of input or output predicates, and has not been previously defined.

In particular, definitions cannot use output predicates.

The following example from the `twin primes` problem contains a valid definition of the predicate `prime/1`.

```
    definition: forall X (prime(X) <-> 2 <= X <= n and not exists D$i M$i (1 < D$i < X and M$i*D$i = X)).
```

#### Assumptions
Atoms within assumptions may use input predicates and predicates defined in a valid definition sequence.

The following assumption comes from a specification defining the expected behavior of a Graph Coloring program.
It uses the two input predicates `edge/2` and `vertex/1`:

```
    assumption: forall X Y (edge(X,Y) -> vertex(X) and vertex(Y)).
```

#### Specs
In addition to predicates valid for assumptions, atoms within specs may also use output predicates.
That is, specs may use all public predicates (input and output) as well as any predicates defined by a valid definition sequence.
Specs with the `universal` annotation are treated as axioms in the `forward` direction of the proof, and as conjectures in the `backward` direction.
A spec with a `forward` annotation is an axiom in the `forward` direction and ignored in the backward direction.
Similarly, a spec with a `backward` annotation is a conjecture in the `backward` direction and ignored in the forward direction.

For example, the following spec from the `twin primes` problem uses the earlier defined predicate `prime/1` to specify the behavior of the output predicate `twins/2`.

```
    spec: forall X Y (twins(X,Y) <-> exists N$ (prime(X) and prime(Y) and X = N$ and N$ + 2 = Y)).
```

The following set of universal specs complete the specification for the Graph Coloring problem introduced earlier:

```
    spec: forall X Z (color(X,Z) -> vertex(X) and color(Z)).
    spec: forall X (vertex(X) -> exists Z color(X,Z)).
    spec: forall X Z1 Z2 (color(X,Z1) and color(X,Z2) -> Z1 = Z2).
    spec: not exists X Y Z (edge(X,Y) and color(X,Z) and color(Y,Z)).
```
