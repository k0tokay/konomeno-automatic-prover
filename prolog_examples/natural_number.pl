plus(zero, X, X).
plus(suc(X), Y, suc(Z)) :- plus(X, Y, Z).

?- plus(suc(suc(zero)), suc(suc(suc(zero))), X).