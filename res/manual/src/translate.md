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

Variables ranging over these sorts are written as `Name$sort`, where `Name` is a capital word and `sort` is one of the sorts defined above.
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

## The Natural Translation (nu)
In many cases, the formulas produced by `tau*` are needlessly complex.
A more natural translation `nu` has been [developed](https://www.cs.utexas.edu/~ai-lab/pub-view.php?PubID=127862) by Lifschitz to produce formulas that are more human-readable, while maintaining HTA-equivalence to their `tau*` counterparts under certain restrictions.
The natural translation `nu` can be safely applied to any rule meeting the requirements of regularity (described in the preceding publication).

`anthem` allows users to apply `nu` to a `mini-gringo` program with the command
```
    anthem translate <program> --with natural
```
which produces the natural translation of the program if every rule is regular, and produces an error about irregularity if not.
For example, the program
```
    composite(I*J) :- I > 1, J > 1.
    prime(I) :- I = 2..10, not composite(I).
```
is translated via the preceding command as
```
    forall I$i J$i (I$i > 1 and J$i > 1 -> composite(I$i * J$i)).
    forall I$i (2 <= I$i <= 10 and not composite(I$i) -> prime(I$i)).
```

## A Combined Translation (mu)
Fandinno and Lifschitz [showed](https://www.cs.utexas.edu/~ai-lab/pub-view.php?PubID=128026) that the translations `tau*` and `nu` can be safely combined by applying `nu` to every regular rule and `tau*` to the rules that are not regular.
The resulting transformation is denoted `mu` -- it can be accessed within `anthem` using the command
```
    anthem translate <program> --with mu
```
If every rule in the program is regular, the outputs of `mu` and `nu` are identical.

## Transformations Within the Target Language

The following transformations translate theories (typically) obtained from applying the `τ*` transformation to a mini-gringo program `Π` into theories whose classical models coincide with the stable models of `Π`.

#### Gamma
The gamma (`γ`) transformation, [introduced](https://doi.org/10.1017/S147106840999010X) by Pearce for propositional programs and extended to first-order programs in [Heuer's Procedure](https://doi.org/10.1007/978-3-031-43619-2_18), was implemented in an unpublished Anthem prototype.
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

#### Simplifications

As mentioned earlier, when using the `mu` translation, regular rules are transformed as `nu`, while
the remaining rules use the `tau*` translation.
However, it is still desirable to simplify the formulas produced by `tau*`,
particularly if a rule is mostly regular.
`anthem` employs three collections of simplifications for this purpose:

* `intuitionistic` simplifications can be safely applied to the result of `tau*`, `nu`, `γ`, or `completion`;
* `ht` simplifications can be similarly applied, and contain some transformations that are not intuitionistically valid;
* `classical` simplifications should only be applied to the result of `γ`, or `completion`, this set of simplifications is an extension of `ht` just as `ht` extends `intuitionistic`.


The `simplify` command allows users to apply any of the preceding portfolios of simplifications to a target language theory.
For example, let `theory.spec` contain the formulas
```
    forall I J V1 (exists I1$i J1$i (V1 = I1$i * J1$i and I1$i = I and J1$i = J) and (exists Z Z1 (Z = I and Z1 = 1 and Z > Z1) and exists Z Z1 (Z = J and Z1 = 1 and Z > Z1)) -> composite(V1)).
    forall I V1 (V1 = I and (exists Z Z1 (Z = I and exists I$i J$i K$i (I$i = 2 and J$i = n and Z1 = K$i and I$i <= K$i <= J$i) and Z = Z1) and exists Z (Z = I and not composite(Z))) -> prime(V1)).
```
Then, the command
```
    anthem simplify theory.spec --portfolio ht --strategy fixpoint
```
produces the ht-equivalent theory
```
    forall I J V1 (exists I1$i J1$i (V1 = I1$i * J1$i and I1$i = I and J1$i = J) and (I > 1 and J > 1) -> composite(V1)).
    forall I V1 (V1 = I and (exists J$i K$i (J$i = n and I = K$i and (2 <= K$i and K$i <= J$i)) and (composite(I) -> #false)) -> prime(V1)).
```

Internally, `anthem` uses these simplifications within verification tasks unless the `--no-simplify` flag is added.
The theories produced by `tau*` or `mu` are subjected to the `ht` simplification portfolio prior to applying `gamma` or `completion`.



###### Intuitionistic Simplifications

The majority of our simplifications are intuitionistically equivalent transformations from one formula `F` to another formula `G` (denoted `F => G`).
These include identities (e.g. `F & true => F`),
annihilations (e.g. `F & false => false`),
and idempotences (e.g. `F & F => F`).


###### Strategies

TODO: Tobias
