in(P, R, 0) :- in0(P, R).
in(P, R, T+1) :- goto(P, R, T).
go(P, T) :- goto(P, R, T ).
in(P, R, T+1) :- in(P, R, T ), not go(P, T), T=0..h-1.
:- in(P, R1, T), in(P, R2, T), R1 != R2.
in_building(P, T) :- in(P, R, T).
:- not in_building(P, T), person(P), T = 0..h.
