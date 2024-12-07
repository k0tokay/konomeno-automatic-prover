% グラフを与える
go(a, b).
go(a, c).
go(b, d).
go(b, e).
go(c, f).
go(d, x).
go(e, x).
go(x, z).
go(y, z).

% 推移律
go(X, Z) :- go(X, Y), go(Y, Z).

?- go(a, X).