c :- d.
d :- c.
p(X) :- r(X), q(X), not c.
p(X) :- r(X), not q(X), c.
