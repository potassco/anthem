dom(1..n).
{q(X1)} :- dom(X1).
p(X) :- q(X).
p'(X) :- q(X), q(Y), X != Y.
diff :- p(X1), not p'(X1).
diff :- p'(X1), not p(X1).
diff :- unsat.
 :- not diff.
