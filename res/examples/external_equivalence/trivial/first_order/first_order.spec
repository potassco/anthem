definition: forall V1 (p(V1) <-> V1 = a or V1 = b).
spec: forall V1 V2 (q(V1, V2) <-> exists X Y (V1 = X and V2 = Y and (exists Z (Z = X and p(Z)) and exists Z (Z = Y and p(Z))))).
