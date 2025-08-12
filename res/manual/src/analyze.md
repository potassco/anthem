# Analyze

The `analyze` command lets users assess properties of their program.


## Predicate Dependency Graph
A predicate dependency graph for a program `Π` has all predicates occurring in `Π` as vertices, and an edge from `p` to `q` if `p` depends on `q`; that is, if `Π` contains a rule of one of the following forms
```
     p  :- ..., q, ...
    {p} :- ..., q, ...
```
An edge `pq` is positive if `q` is neither negated nor doubly negated.


## Tightness
A program is tight if its predicate dependency graph has no cycles consisting of positive edges.
Users can check their programs for tightness with the command
```
    anthem analyze program.lp --property tightness
```

## Regularity
Regular rules represent a broad syntactic fragment of the mini-gringo language.
They forbid terms of certain forms -- primarily terms that do not have exactly one value, such as
```
    2/X, 3 × (X..Y), a+1, a..5
```
Users can check their programs for regularity with the command
```
    anthem analyze program.lp --property regularity
```
