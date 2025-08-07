dom(100 * 50).
dom(1..n).
{q(X1)} :- dom(X1).
p(X) :- q(X), X != 100 * 50.
p'(X) :- q(X).
diff :- p(X1), not p'(X1).
diff :- p'(X1), not p(X1).
 :- not diff.
