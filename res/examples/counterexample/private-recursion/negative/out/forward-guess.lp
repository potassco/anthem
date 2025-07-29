dom(1..n).
{q(X1)} :- dom(X1).
{r(X1)} :- dom(X1).
a :- not b.
b :- not a.
p(X) :- r(X), q(X), a.
p(X) :- r(X), not q(X), b.
holds(q(X1)) :- q(X1).
holds(r(X1)) :- r(X1).
holds(p(X1)) :- p(X1).
