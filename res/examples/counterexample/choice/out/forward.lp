dom(1..n).
{p}.
p' :- p.
diff :- p, not p'.
diff :- p', not p.
 :- not diff.
