p(X, N + 1) :- q(X, N), N >= 0.
q(X, N + 1) :- p(X, N), N >= 0.
p(X) :- p(X, N), N >= 0.
q(X) :- q(X, N), N >= 0.
