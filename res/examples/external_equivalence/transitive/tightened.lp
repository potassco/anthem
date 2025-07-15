t(X, Y, N + 1) :- e(X, Y, N), N >= 0.
t(X, Y, N + 1) :- e(X, Z, N), t(Z, Y, N), N >= 0.
e(a1, a2, N + 1) :- N >= 0.
e(a2, a1, N + 1) :- N >= 0.
t(X, X1) :- t(X, X1, N), N >= 0.
e(X, X1) :- e(X, X1, N), N >= 0.
