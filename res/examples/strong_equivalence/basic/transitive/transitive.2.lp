{q(X, Y)} :- p(X), p(Y).
:- q(X, Y), q(Y, Z), not q(X, Z), p(X), p(Y), p(Z).
