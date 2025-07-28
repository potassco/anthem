orphan(X) :- living(X), father(Y,X), mother(Z,X),
             not living(Y), not living(Z).
