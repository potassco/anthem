# Finding counterexamples for external equivalence problems

Given an external equivalence problem with files: `p.lp`, `q.lp`, `eq.ug`, we can generate programs that find counterexamples for this external equivalence problem with the command:
```
anthem falsify p.lp q.lp eq.ug
```
By default this prints the checking programs (separated by comments stating the name of each file) as well as some info messages before the programs.
To write the programs to files add the argument `--save-files` followed by the directory that the files should be written to.

`anthem` checks whether the standard transformation is applicable or whether the guess and check transformation has to be used.
The property that needs to hold for the standard transformation is currently called "private weak stratification".
A program fulfills this property if it does not contain: (1) choices over private predicates, and (2) negative cycles through only private predicates (using the standard predicate dependency graph with positive and negative edges).
`anthem` will print a message if a program is detected to not have "private weak stratification".

For the standard transformation counterexample can the be found by running the generated logic program(s) with `clingo` as follows:
```
clingo forward.lp -c n=0
```
This command checks for counterexamples in the forward direction with a domain size of 0.
The domain size can then be increased by setting `n` to higher values.

If the guess and check transformation was used counterexamples can be computed with `gc.py` as follows:
```
gc.py forward-guess -C forward-check
```
But the guess program needs to be modified to set the constant `n` by adding the line
```
#const n=0.
```
with whatever domain size should be checked.

The use of the guess and check transformation can be disabled by using the option `--no-gc`.
However, this may result in checking programs that find false counterexamples.
For example, see the external equivalence problem in `private-recursion/negative`.

It is also possible to generate the checking program for computing counterexamples in a specific direction.
Adding `--direction forward` only produces the forward program that check if `p.lp` has a model which is not a model of `q.lp` and vice verse for `--direction backward`.
