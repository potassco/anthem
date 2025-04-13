assumption: forall M (sqrtb(M) <-> exists J$i K1$i (J$i = b and 1 <= K1$i <= J$i and M = K1$i and K1$i * K1$i <= b and (K1$i + 1) * (K1$i + 1) > b)).
assumption: forall V1 (composite(V1) <-> exists I2$i J2$i J1$i exists J$i (V1 = I2$i * J2$i and sqrtb(J1$i) and 2 <= I2$i <= J1$i and J$i = b and 2 <= J2$i <= J$i)).
spec: forall I (prime(I) <-> exists I$i J$i K1$i (I$i = a and J$i = b and I$i <= K1$i <= J$i and I = K1$i and not composite(I))).

% This is the result of COMP(SIMPLIFY(tau-star-v1(primes.3.lp)))
