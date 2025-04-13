# `primes/optimized`

## Usage
```
anthem verify --equivalence=external primes.2.lp primes.3.spec primes.ug primes.po
anthem verify --equivalence=external primes.3.lp primes.3.spec primes.ug primes.po
```

## Origin
This is an attempt to verify the external equivalence of primes.2.lp and primes.3.lp transitively, 
by establishing their external equivalence to a first-order specification obtained by 
simplifying the second-order completion of primes.3.lp.
