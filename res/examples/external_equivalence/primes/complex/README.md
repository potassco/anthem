# `primes/complex`

## Usage
```
anthem verify --equivalence=external primes.1.lp primes.2.lp primes.ug
anthem verify --equivalence=external primes.2.lp primes.3.lp primes.ug primes.po -t 600 -m 6
anthem verify --equivalence=external primes.2.lp primes.spec primes.ug -t 600 -m 6
```

## Origin
This example was taken from

> Jorge Fandinno, Zachary Hansen, Yuliya Lierler, Vladimir Lifschitz, Nathan Temple.
> External Behavior of a Logic Program and Verification of Refactoring. TPLP 23(4): 933-947 (2023).
> https://doi.org/10.1017/S1471068423000200
