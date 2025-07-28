dom(1..n).
{q(X1)} :- dom(X1).
{r(X1)} :- dom(X1).
c :- not d.
d :- not c.
p(X) :- r(X), q(X), c.
p(X) :- r(X), not q(X), d.
a :- not b.
b :- not a.
p'(X) :- r(X), q(X), a.
p'(X) :- r(X), not q(X), b.
diff :- p(X1), not p'(X1).
diff :- p'(X1), not p(X1).
 :- not diff.
