{in_cover(1..n)}.
:- I != J, in_cover(I), in_cover(J), s(X,I), s(X,J).
covered(X) :- in_cover(I), s(X,I).
:- s(X,I), not covered(X).
