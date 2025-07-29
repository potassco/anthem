a :- not b.
b :- not a.
p'(X) :- r(X), q(X), a.
p'(X) :- r(X), not q(X), b.
diff :- p(X1), not p'(X1).
diff :- p'(X1), not p(X1).
diff :- unsat.
 :- diff.
q(X1) :- holds(q(X1)).
r(X1) :- holds(r(X1)).
p(X1) :- holds(p(X1)).
