# `private-recursion/negative`

The following command generates the guess and check logic program for the forward and backward direction in the `out` directory.
```
anthem falsify negative.1.lp negative.2.lp negative.ug --save-files out
```

These files can then be used as the input to `guess_and_check`.
However, one further modification is needed: `guess_and_check` does not support passing the value for the domain size constant (i.e. `-c n=1`).
Therefore, we have to add the following line to the `forward-guess.lp`/`backward-guess.lp` file:
```
#const n=1.
```
The value of the constant then has to be changed by modifying this line.

We can also instead disable the guess and check transformation and just use the standard one by adding the `--no-gc` argument to the above `anthem` command.
But as the example programs do not fulfill the conditions of the standard transformation (as reported by `anthem`) the resulting equivalence checking programs are not correct.
Indeed, in both directions we obtain counterexamples, even though the programs are externally equivalent.
