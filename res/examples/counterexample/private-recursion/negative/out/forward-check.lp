c :- not d.
d :- not c.
p'(X) :- r(X), q(X), c.
p'(X) :- r(X), not q(X), d.
diff :- p(X1), not p'(X1).
diff :- p'(X1), not p(X1).
 :- diff.
q(X1) :- holds(q(X1)).
r(X1) :- holds(r(X1)).
p(X1) :- holds(p(X1)).
