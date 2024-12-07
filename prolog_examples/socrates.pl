human(taro).
human(socrates).
greek(socrates).
mortal(X) :- human(X).

?- greek(X), mortal(X).