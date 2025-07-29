dom(1..n).
{q(X1)} :- dom(X1).
{r(X1)} :- dom(X1).
a :- b.
b :- a.
p(X) :- r(X), q(X), not a.
p(X) :- r(X), not q(X), a.
c :- d.
d :- c.
p'(X) :- r(X), q(X), not c.
p'(X) :- r(X), not q(X), c.
diff :- p(X1), not p'(X1).
diff :- p'(X1), not p(X1).
diff :- unsat.
 :- not diff.
