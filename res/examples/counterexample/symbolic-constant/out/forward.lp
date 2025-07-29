dom(1..n).
{q(X1)} :- dom(X1).
p(X) :- q(X).
p'(X) :- q(X), X != a.
diff :- p(X1), not p'(X1).
diff :- p'(X1), not p(X1).
diff :- unsat.
 :- not diff.
