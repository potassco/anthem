# Non-Tight Program

We want to verify that `non_tight.lp` implies the specification `non_tight.spec` under the user guide `non_tight.ug`.
I.e., the backward direction of external equivalence.

We can not do so directly, as running
```
anthem verify --equivalence external --direction backward non-tight.lp non-tight.ug non-tight.spec
```
results in an error that the program is not tight (and as it is not locally tight we can not just add the `--bypass-tightness` flag).

After tightening the program we have a locally tight program (result saved in `tightened.lp`).
Therefore, we can add the flag `--bypass-tightness`.
But we still get an error by running
```
anthem verify --equivalence external --direction backward tightened.lp non-tight.ug non-tight.spec --bypass-tightness
```
as we now have private recursion.

Thus, we need to adjust the user guide to include the predicates that were introduced by tightening (`p/2` and `q/2`) to the output symbols.
This results in the user guide `tightened.ug`.
Now we can run the command

```
anthem verify --equivalence external --direction backward tightened.lp tightened.ug non-tight.spec --bypass-tightness
```
