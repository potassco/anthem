dom(1..n).
{n(X1)} :- dom(X1).
{e(X1, X2)} :- dom(X1), dom(X2).
t(X, Y) :- n(X), n(Y), e(X, Y).
t(X, Y) :- n(X), n(Y), n(Z), e(X, Z), not not t(Z, Y).
t'(X, Y) :- n(X), n(Y), e(X, Y).
t'(X, Y) :- n(X), n(Y), n(Z), e(X, Z), t'(Z, Y).
diff :- t(X1, X2), not t'(X1, X2).
diff :- t'(X1, X2), not t(X1, X2).
 :- not diff.
