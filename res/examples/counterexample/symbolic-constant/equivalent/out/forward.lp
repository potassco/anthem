dom(a).
dom(b).
dom(1..n).
{q(X1)} :- dom(X1).
{r(X1, X2)} :- dom(X1), dom(X2).
p(X) :- q(X), not r(X, a).
p'(X) :- q(X), not r(X, a).
p'(X) :- q(X), r(X, b).
diff :- p(X1), not p'(X1).
diff :- p'(X1), not p(X1).
 :- not diff.
