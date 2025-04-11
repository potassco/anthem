# Verification
The `verify` command uses the ATP [vampire](https://vprover.github.io/) to automatically verify that some form of equivalence holds between two programs, or between a program and a target language specification.
These equivalence types are described below.
By default, Anthem verifies equivalence -- this can also be specified by adding the `--direction universal` flag.
To verify one implication of the equivalence (e.g. \\(\rightarrow\\)) add the `--direction forward` flag (conversely, the `--direction backward` flag for \\(\leftarrow\\)).


## Strong Equivalence
Strong equivalence is a property that holds for a pair of programs (`Π1`, `Π2`) if `Π1 U Π` has the same answer sets as `Π2 U Π`, for any program `Π`.
This property can be verified for mini-gringo programs by determining the equivalence of `τ*Π1` and `τ*Π2` within the [HTA](https://doi.org/10.1017/S1471068421000338) (here-and-there with arithmetic) deductive system.
This problem can be reduced to a first-order reasoning task by applying the gamma transformation, e.g. determining the equivalence of `γτ*Π1` and `γτ*Π2`.
The property can be automatically verified with the command
```
    anthem verify --equivalence strong p1.lp p2.lp
```

We can additionally specify the translation used to obtain the HTA representation of our programs.
Valid options are `tau*` (the default) or `mu`, which can be enabled with the command
```
    anthem verify --equivalence strong <programs> --formula-representation mu
```


## External Equivalence
Strong equivalence is sometimes too strong of a condition.
Sometimes we are interested in the behavior of only certain program predicates when the program is paired with a user guide defining the context in which the program should be used.
This is referred to as [external behavior](https://doi.org/10.1017/S1471068423000200).

As an example, consider the programs
```
    composite(I*J) :- I > 1, J > 1.
    prime(I) :- I = 2..n, not composite(I).
```
and
```
    composite(I*J) :- I = 2..n, J = 2..n.
    prime(I) :- I = 2..n, not composite(I).
```
paired with the user guide
```
    input: n -> integer.
    output: prime/1.
```
This user guide indicates that `n` is a placeholder -- that is, `n` is a symbolic constant that may be treated in a non-Herbrand way.
Specifically, `n` is to be interpreted as an integer.
The second line of the user guide declares that the external behavior of these programs is defined by the extent of the `prime/1` predicate.
If these extents coincide for all interpretations that interpret `n` as an integer, then we consider the programs externally equivalent.

Anthem can verify this claim automatically with the command
```
    anthem verify --equivalence external <SPECIFICATION> <PROGRAM> <USER GUIDE> --direction universal
```
This amounts to confirming that the program implements the specification under the assumptions of the user guide.
This is done by transforming the program(s) into their formula representations using the `τ*` and `COMP` transformations, then deriving their equivalence.

Note that the `universal` direction is the default, and may be dropped.
To verify that the program posesses a certain property expressed by the specification, set the direction to backward (`--direction backward`).
To verify that the program's external behavior is a consequence of the specification, set the direction to forward (`--direction forward`).

Currently, external equivalence only supports `tau*` as a valid option for `--formula-representation`.


#### Tightness and Private Recursion
External equivalence can only be verified automatically if the program(s) are tight.
Anthem checks this condition by default when `verify` is invoked.
It may be that a non-tight program is [locally tight](https://doi.org/10.1017/S147106842300039X).
If a user is certain that their program is locally tight, then the tightness check can be bypassed by providing the flag `--bypass-tightness`.

A program contains private recursion with respect to a user guide if
* its predicate dependency graph has a cycle such that every vertex in it is a private symbol or
* it includes a choice rule with a private symbol in the head.
During external equivalence verification, any logic program is subjected to a test for private recursion and rejected if it occurs.
This step cannot be bypassed.

#### Renaming Private Predicates
In the example above, `prime/1` is a public predicate, and both definitions of `composite/1` are private predicates.
The predicates named `composite/1` are two different predicates, but they have conflicting names.
In such a case, the conflicting predicate from the program is renamed with an `_p`, e.g. `composite_p/1`.

#### Replacing Placeholders
Syntactically, `n` is a symbolic constant, but it has been paired with a user guide specifying that it should be interpreted as an integer.
However, the standard interpretations of interest interpret symbolic constants and numerals as themselves.
Thus, in an external equivalence verification task, we replace every occurrence of a symbolic constant `n` with an integer-sorted function constant named `n`, e.g. `n$i`.
This applies to all files involved: programs, specifications, user guides, and proof outlines.
Thus, while running the example above, you could expect to see such output as
```
> Proving forward_problem_0...
Axioms:
    forall V1 (composite(V1) <-> exists I J (exists I1$i J1$i (V1 = I1$i * J1$i and I1$i = I and J1$i = J) and (exists Z Z1 (Z = I and Z1 = 1 and Z > Z1) and exists Z Z1 (Z = J and Z1 = 1 and Z > Z1))))
    forall V1 (composite_p(V1) <-> exists I J (exists I1$i J1$i (V1 = I1$i * J1$i and I1$i = I and J1$i = J) and (exists Z Z1 (Z = I and exists I$i J$i K$i (I$i = 2 and J$i = n$i and Z1 = K$i and I$i <= K$i <= J$i) and Z = Z1) and exists Z Z1 (Z = J and exists I$i J$i K$i (I$i = 2 and J$i = n$i and Z1 = K$i and I$i <= K$i <= J$i) and Z = Z1))))
    forall V1 (prime(V1) <-> exists I (V1 = I and (exists Z Z1 (Z = I and exists I$i J$i K$i (I$i = 2 and J$i = n$i and Z1 = K$i and I$i <= K$i <= J$i) and Z = Z1) and exists Z (Z = I and not composite(Z)))))

Conjectures:
    forall V1 (prime(V1) -> exists I (V1 = I and (exists Z Z1 (Z = I and exists I$i J$i K$i (I$i = 2 and J$i = n$i and Z1 = K$i and I$i <= K$i <= J$i) and Z = Z1) and exists Z (Z = I and not composite_p(Z)))))
> Status:
    Theorem
```

for each problem.
The (problem name, axioms, conjecture) triple is printed as soon as the ATP is invoked, and the status (indicating if the ATP proved the conjecture from the axioms successfully) is printed once the ATP invocation returns.
If all the problems are proven (Theorem status) then Anthem reports success on the verification task.



### Answer Set Equivalence
Answer set equivalence (which asserts two programs have the same answer sets) is a special case of external equivalence.
A user guide without placeholders, assumptions or input declarations, that contains every predicate in a pair of programs `(Π1, Π2)` as an output declaration, can be used to validate the answer set equivalence of `Π1` and `Π2`.

## Interpreting Anthem Output
Anthem will pass a series of problems to an ATP backend and report the status of each using the [SZS status ontology](https://dblp.org/rec/conf/lpar/Sutcliffe08.bib).
If all problems are successfully verified, Anthem will report
```
    Success!
```
which indicates that the equivalence property holds.

Otherwise, Anthem will report
```
    Failure!
```
indicating that the equivalence property could not be verified.
Note that this is NOT a proof that the equivalence property does not hold.


## Problem Files vs End-to-end Use
Rather than invoking `vampire`, Anthem can produce a set of TPTP problem files that can be passed manually to a variety of ATPs.
If each problem is verified (the ATP reports a `Theorem` SZS status), then the verification can be considered successfully verified.
To invoke this option, add the `--no-proof-search` flag to a verification command, along with `--save-problems <DIR>` to save problem files to a directory of choice.


## Additional Options

Adding a `--no-simplify` flag disables the HT-equivalent simplifications that are automatically applied to the theory `COMP[τ*Π]`.

Adding a `--no-eq-break` flag disables "equivalence breaking."
When equivalence breaking is enabled, Anthem turns every conjecture of the form
\\[\forall X F(X) \leftrightarrow G(X)\\]
into a pair of conjectures
\\[\forall X F(X) \rightarrow G(X), \forall X G(X) \rightarrow F(X)\\]
which are passed to `vampire` separately.

Anthem can parallelize at the problem level with the `--prover-instances` (`-n`) argument -- this determines how many instances of the backend ATP are invoked.
It can also pass parallelism arguments to the ATP.
`--prover-cores` (`-m`) determines how many threads each ATP instance can use.
The `--time-limit` flag (`-t`) is the time limit in seconds to prove each problem passed to an ATP.
