a :- b.
b :- a.
p(X) :- r(X), q(X), not a.
p(X) :- r(X), not q(X), a.
