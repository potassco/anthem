# Translation

## The mini-gringo Dialect
The [mini-gringo](https://doi.org/10.1017/S1471068420000344) dialect is a subset of the language supported by the answer set solver [clingo](https://potassco.org/clingo/).
It has been extensively studied within the ASP literature as a theoretical language whose semantics can be formally defined via transformations into first-order theories interpreted under the semantics of here-and-there (with arithmetic).

A mini-gringo program consists of three types of rules: choice, basic, and constraint:

```
    {H} :- B1, ..., Bn.
     H  :- B1, ..., Bn.
        :- B1, ..., Bn.
```

where `H` is an atom and each `Bi` is a singly, doubly, or non-negated atom or comparison.


## The Target Language
The formula representation language (often called the "target" of ASP-to-FOL transformations) is a many-sorted first-order language.
Specifically, all terms occurring in a mini-gringo program belong to the language's supersort, `general` (abbreviated `g`).
It contains two special terms, `#inf` and `#sup`, representing the minimum and maximum elements in the total order on general terms.
Numerals (which have a one-to-one correspondence with integers) are a subsort of this sort, they belong to a sort referred to as `integer` (abbreviated `i`).
All other general terms are symbolic constants, they belong to the `symbol` sort (abbreviated `s`).

Variables ranging over these sorts are written as `name$sort`, where `name` is a capital word and `sort` is one of the sorts defined above.
Certain abbreviations are permitted; the following are examples of valid variables:

```
    V$general, V$g, V
    X$integer, X$i, X$
    Var$symbol, Var$s
```

These lines represent equivalent ways of writing a general variable named `V`, an integer variable named `X`, and a symbol variable named `Var`.



## The Formula Representation Transformation (tau*)

The transformation referred to in the literature as `tau*` (`τ*`) is a collection of transformations from mini-gringo programs into the syntax of first-order logic, taking special consideration for the fact that while an ASP term can have 0, 1, or many values, a first-order term can have only one.
In the presence of arithmetic terms or intervals, such as `1/0` or `0..9`, this introduces translational complexities.
Interested readers should refer [here](https://doi.org/10.1017/S1471068420000344) for details.

The tau* transformation is fundamental to Anthem.
For a mini-gringo program `Π`, the HTA (here-and-there with arithmetic) models of the formula representation `τ*Π` correspond to the stable models of `Π`.
Furthermore, additional transformations can, in certain cases, produce formula representations within the same language whose classical models capture the behavior of `Π`.

Access the `τ*` transformation via the `translate` command, e.g.
```
    anthem translate program.lp --with tau-star
```

## Tau* with Counting Aggregates

If the program contains counting aggregates, it is also necessary to generate a set of supporting axioms for any theory produced by `tau*`.
For instance, the command
```
    anthem translate program.lp --with tau-star --include-axioms
```
displays both the axioms defining `start`, `atmost`, and `atleast` as they are used within the theory `tau*(Π)`, and `Π` itself.

These axioms include the 3 axioms defining `start` for each `start` atom used within the theory, 
an induction axiom for each `start` atom used within the theory, 
and an axiom defining `atmost` or `atleast` for each counting aggregate occurring in the program.

For a program `Π`, we call this set of axioms `C(Π)` - the counting axioms of `Π`.




## Transformations Within the Target Language

The following transformations translate theories (typically) obtained from applying the `τ*` transformation to a mini-gringo program `Π` into theories whose classical models coincide with the stable models of `Π`.

#### Gamma
The gamma (`γ`) transformation ([introduced](https://doi.org/10.1017/S147106840999010X) by Pearce for propositional programs) and extended to first-order programs in [Heuer's Procedure](https://doi.org/10.1007/978-3-031-43619-2_18) was implemented in an unpublished Anthem prototype.
The implementation of this system follows the description found [here](https://doi.org/10.1007/978-3-031-43619-2_18).
For a predicate `p`, a new predicate representing satisfaction in the "here" world named `hp` is introduced.
Similarly, predicate `tp` represents satisfaction of `p` in the "there" world.
Thus, for a theory
```
    forall X ( exists I$ (X = I$ and 3 < I$ < 5) -> p(X) ).
```
`gamma` produces
```
    forall X ((exists I$i (X = I$i and 3 < I$i < 5) -> hp(X)) and (exists I$i (X = I$i and 3 < I$i < 5) -> tp(X))).
```
Access the `gamma` transformation via the `translate` command, e.g.
```
    anthem translate theory.spec --with gamma
```
<!-- or stack it with the `τ*` command, e.g.
```
    anthem translate program.lp --with tau-star,gamma
``` -->


#### Completion

This is an implementation of an [extension](https://doi.org/10.1017/S147106842300039X) of [Clark's Completion](https://doi.org/10.1007/978-1-4684-3384-5_11).
It accepts a completable theory (such as those produced by `τ*`) and produces the (first-order) completion.
For example, the completion of the theory
```
    forall X ( X = 1 -> p(X) ).
    forall X Y ( q(X,Y) -> p(X) ).
```
is
```
    forall X ( p(X) <-> X = 1 or exists Y q(X,Y) ).
```

Access the `completion` transformation via the `translate` command, e.g.
```
    anthem translate theory.spec --with completion
```
<!-- or stack it with the `τ*` command, e.g.
```
    anthem translate program.lp --with tau-star,completion
``` -->
However, keep in mind that the original program must be tight for the models of the completion to coincide with the stable models of the program!
This property is not checked automatically during translation.
