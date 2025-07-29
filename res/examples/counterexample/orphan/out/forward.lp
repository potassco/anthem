dom(1..n).
{father(X1, X2)} :- dom(X1), dom(X2).
{mother(X1, X2)} :- dom(X1), dom(X2).
{living(X1)} :- dom(X1).
parent_living(X) :- father(Y, X), living(Y).
parent_living(X) :- mother(Y, X), living(Y).
orphan(X) :- living(X), not parent_living(X).
orphan'(X) :- living(X), father(Y, X), mother(Z, X), not living(Y), not living(Z).
diff :- orphan(X1), not orphan'(X1).
diff :- orphan'(X1), not orphan(X1).
diff :- unsat.
 :- not diff.
