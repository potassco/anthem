a :- not b.
b :- not a.
p(X) :- r(X), q(X), a.
p(X) :- r(X), not q(X), b.
