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

A "regular program" is a program consisting only of regular rules (see below). The regularity of a program can be checked with the command
```
    anthem analyze program.lp --property regularity
```
A rule fulfilling the following restricitions is called "regular":
Its body contains only terms regular of first kind and/or comparisons of first or second kind. No nested rules and aggregates are allowed.
Its head is either empty (constraint), an atom (basic rule) or an atom in braces (choice rule). It contains only terms regular of first and/or second kind.

A term is called "regular of first kind" if it
- is a Variable
- is a precomputed term, i.e.
    - is a symbolic constant, #inf or #sup
    - it is an integer
- makes use of only Multiplication, Addition and Substraction and does not contain symbolic constants, #inf or #sup.

A term is called "regular of second kind" if it is of form t1..t2 where t1 and t2 are regular of first kind and do not contain symbolic constants, #inf or #sup.

A "comparison of first kind" is of form "t1 c t2" where t1 and t2 are regular of first kind and c is any comparison operator.
A "comparison of second kind" is of form "t1=t2", where t1 is regular of first kind and t2 is regular of second kind
