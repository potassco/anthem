dom(1..n).
{q(X1)} :- dom(X1).
{r(X1)} :- dom(X1).
c :- not d.
d :- not c.
p(X) :- r(X), q(X), c.
p(X) :- r(X), not q(X), d.
holds(q(X1)) :- q(X1).
holds(r(X1)) :- r(X1).
holds(p(X1)) :- p(X1).
