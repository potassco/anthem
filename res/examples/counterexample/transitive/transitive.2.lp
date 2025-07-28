t(X,Y) :- n(X), n(Y), e(X,Y).
t(X,Y) :- n(X), n(Y), n(Z), e(X,Z), not not t(Z,Y).
