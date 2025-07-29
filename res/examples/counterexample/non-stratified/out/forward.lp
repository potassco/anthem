dom(1..n).
p :- not q.
q :- not p.
p' :- not q.
q' :- not p.
diff :- p, not p'.
diff :- p', not p.
diff :- q, not q'.
diff :- q', not q.
diff :- unsat.
 :- not diff.
