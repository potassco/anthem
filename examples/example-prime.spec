input: n -> integer.
output: prime/1.

assume: n >= 1.

spec: forall X (prime(X) -> exists N (X = N)).
spec: forall N (prime(N) <-> N > 1 and N <= n and not exists I, J (I > 1 and J > 1 and I * J = N)).
