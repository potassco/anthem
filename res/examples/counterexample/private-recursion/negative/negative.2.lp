c :- not d.
d :- not c.
p(X) :- r(X), q(X), c.
p(X) :- r(X), not q(X), d.
