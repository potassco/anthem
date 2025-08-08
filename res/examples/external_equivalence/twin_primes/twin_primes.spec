definition: forall X (prime(X) <-> 2 <= X <= n and not exists D$i M$i (1 < D$i < X and M$i*D$i = X)).
spec: forall X Y (twins(X,Y) <-> exists N$ (prime(X) and prime(Y) and X = N$ and N$ + 2 = Y)).
