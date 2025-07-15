t(X,Y) :- e(X,Y).
t(X,Y) :- e(X,Z), t(Z,Y).
e(a1,a2).
e(a2,a1).
