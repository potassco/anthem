# `orphan`

## Usage

Note that the programs are not externally equivalent under user guide `orphan.a.ug`,
but `orphan.b.ug` adds missing assumptions under which the programs are indeed externally equivalent.

```
anthem verify --equivalence external orphan.1.lp orphan.2.lp orphan.b.ug
```

## Output
To understand what output is expected, have a look into the [out](./out) subfolder.

## Origin
This example was taken from

> Jorge Fandinno, Zachary Hansen, Yuliya Lierler, Vladimir Lifschitz, Nathan Temple.
> External Behavior of a Logic Program and Verification of Refactoring. TPLP 23(4): 933-947 (2023).
> https://doi.org/10.1017/S1471068423000200
