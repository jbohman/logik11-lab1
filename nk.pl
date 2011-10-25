verify(InputFileName) :- 
    see(InputFileName),
    read(Prems), read(Goal), read(Proof),
    seen,
    valid_fwd(Prems, Goal, Proof).

valid_fwd(Prems, Goal, Proof):-
    reverse(Proof, RevProof),
    valid_rev(Prems, Goal, RevProof).

valid_rev(Prems, Goal, RevProof):-
    RevProof = [[_, Goal, X]|_], /* Goal at end of Proof */
    X \= assumption,
    X \= copy(_),
    flatten(RevProof, Frp),
    valid(Prems, RevProof, Frp).

valid(_,[],_).

% assumption
valid(_, [[_,_,assumption]|[]], _).

% premise
valid(Prems, [[X,Y,premise]|Rest], Frp):-
    select([X,Y,premise], Frp, NewFrp),
    number(X),
    prop(Y),
    member(Y, Prems),
    %write('premise\n'),
    valid(Prems, Rest, NewFrp).


% copy(x)
valid(Prems, [[X,Y,Z]|Rest], Frp):-
    select([X,Y,Z], Frp, NewFrp),
    number(X),
    prop(Y),
    Z = copy(A),
    member([A,Y,_], NewFrp),
    %write('copy(x)\n'),
    valid(Prems, Rest, NewFrp).


% andint(x,y)
valid(Prems, [[X,Y,Z]|Rest], Frp):-
    select([X,Y,Z], Frp, NewFrp),
    number(X),
    prop(Y),
    Z = andint(A,B),
    member([A, C, _], NewFrp),
    member([B, D, _], NewFrp),
    Y == and(C,D),
    %write('andint(x,y)\n'),
    valid(Prems, Rest, NewFrp).

% andel1(x)
valid(Prems, [[X,Y,Z]|Rest], Frp):-
    select([X,Y,Z], Frp, NewFrp),
    number(X),
    prop(Y),
    Z = andel1(A),
    member([A, B, _], NewFrp),
    B = and(D, _),
    Y == D,
    %write('andel1(x)\n'),
    valid(Prems, Rest, NewFrp).

% andel2(x)
valid(Prems, [[X,Y,Z]|Rest], Frp):-
    select([X,Y,Z], Frp, NewFrp),
    number(X),
    prop(Y),
    Z = andel2(A),
    member([A, B, _], NewFrp),
    B = and(_, E),
    Y == E,
    %write('andel2(x)\n'),
    valid(Prems, Rest, NewFrp).


% orint1(x)
valid(Prems, [[X,Y,Z]|Rest], Frp):-
    select([X,Y,Z], Frp, NewFrp),
    number(X),
    prop(Y),
    Z = orint1(A),
    Y = or(B,C), % expand Y to or(B,C)
    member([A, B, _], NewFrp), % do B exist
    prop(B), % is B a prop
    prop(C), % is C a prop
    %write('orint1(x)\n'),
    valid(Prems, Rest, NewFrp).

% orint2(x)
valid(Prems, [[X,Y,Z]|Rest], Frp):-
    select([X,Y,Z], Frp, NewFrp),
    number(X),
    prop(Y),
    Z = orint2(A),
    Y = or(B,C), % expand Y to or(B,C)
    member([A, C, _], NewFrp), % do C exist
    prop(B), % is B a prop
    prop(C), % is C a prop
    %write('orint2(x)\n'),
    valid(Prems, Rest, NewFrp).

% orel(x,y,u,v,w)
valid(Prems, [[X,Y,Z]|Rest], Frp):-
    select([X,Y,Z], Frp, NewFrp),
    number(X),
    prop(Y),
    Z = orel(A,B,C,D,E),
    member([A, F, _], NewFrp),
    F = or(G,H),
    member([B, G, assumption], NewFrp),
    member([C, I, _], NewFrp),
    member([D, H, assumption], NewFrp),
    member([E, J, _], NewFrp),
    I == J,
    J == Y,
    %write('orel(x,y,u,v,w)\n'),
    valid(Prems, Rest, NewFrp).


% impint(x,y)
valid(Prems, [[X,Y,Z]|Rest], Frp):-
    select([X,Y,Z], Frp, NewFrp),
    number(X),
    prop(Y),
    B is (X-1),
    Z = impint(A,B),
    Y = imp(C,D),
    member([A,C,assumption], NewFrp),
    member([B,D,_], NewFrp),
    %write('impint(x,y)\n'),
    valid(Prems, Rest, NewFrp).

% impel(x,y)
valid(Prems, [[X,Y,Z]|Rest], Frp):-
    select([X,Y,Z], Frp, NewFrp),
    number(X),
    prop(Y),
    Z = impel(A,B),
    member([B, imp(F,Y), _], NewFrp),
    member([A, F, _], NewFrp),
    %write('impel(x,y)\n'),
    valid(Prems, Rest, NewFrp).


% negint(x,y)
valid(Prems, [[X,Y,Z]|Rest], Frp):-
    select([X,Y,Z], Frp, NewFrp),
    number(X),
    prop(Y),
    Y = neg(E),
    Z = negint(A,B),
    member([A, E, assumption], NewFrp),
    member([B, cont, _], NewFrp),
    %write('negint(x,y)\n'),
    valid(Prems, Rest, NewFrp).

% negel(x,y)
valid(Prems, [[X,Y,Z]|Rest], Frp):-
    select([X,Y,Z], Frp, NewFrp),
    number(X),
    prop(Y),
    Y = cont,
    Z = negel(A,B),
    member([A, C, _], NewFrp),
    member([B, D, _], NewFrp),
    D == neg(C),
    %write('negel(x,y)\n'),
    valid(Prems, Rest, NewFrp).


% contel(x) TODO
valid(Prems, [[X,Y,Z]|Rest], Frp):-
    select([X,Y,Z], Frp, NewFrp),
    number(X),
    prop(Y),
    Z = contel(A),
    member([A, cont, _], NewFrp),
    %write('contel(x)'),
    valid(Prems, Rest, NewFrp).


% negnegint(x)
valid(Prems, [[X,Y,Z]|Rest], Frp):-
    select([X,Y,Z], Frp, NewFrp),
    number(X),
    prop(Y),
    Z = negnegint(A),
    member([A, B, _], NewFrp),
    prop(B),
    Y == neg(neg(B)),
    %write('negnegint(x)\n'),
    valid(Prems, Rest, NewFrp).

% negnegel(x)
valid(Prems, [[X,Y,Z]|Rest], Frp):-
    select([X,Y,Z], Frp, NewFrp),
    number(X),
    prop(Y),
    Z = negnegel(A),
    member([A, B, _], NewFrp),
    prop(B), % B == neg(neg(Y)) ?
    %write('negnegel(x)\n'),
    valid(Prems, Rest, NewFrp).


% mt(x,y) TODO
valid(Prems, [[X,neg(Y),Z]|Rest], Frp):-
    select([X,neg(Y),Z], Frp, NewFrp),
    number(X),
    prop(Y),
    Z = mt(A,B),
    member([A, imp(Y,D), _], NewFrp),
    member([B, neg(D), _], NewFrp),
    %write('mt(x,y)'),
    valid(Prems, Rest, NewFrp).


% pbc(x,y)
valid(Prems, [[X,Y,Z]|Rest], Frp):-
    select([X,Y,Z], Frp, NewFrp),
    number(X),
    prop(Y),
    Z = pbc(A,B),
    member([A, neg(Y), assumption], NewFrp),
    member([B, cont, _], NewFrp),
    %write('pbc(x,y)\n'),
    valid(Prems, Rest, NewFrp).

% lem
valid(Prems, [[X,Y,lem]|Rest], Frp):-
    select([X,Y,lem], Frp, NewFrp),
    number(X),
    prop(Y),
    Y = or(A,neg(A)),
    valid(Prems, Rest, NewFrp).

% we are box
valid(Prems, [Box|Rest], Frp):-
    is_box(Box),
    reverse(Box, RevBox),
    valid(Prems, RevBox, Frp),
    valid(Prems, Rest, Frp).

is_box([[A, _, assumption]|_]):-
    number(A).

flatten([],[]).
flatten([[]|L],L).
flatten([X|L1],[X|L2]) :- X = [A,B,_], number(A), prop(B), flatten(L1,L2).
flatten([X|L1],L4) :- flatten(X,L2),
                      flatten(L1,L3),
                      append(L2,L3,L4).

% Propositioner

prop(X):-
    member(X,[a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,u,v,w,x,y,z]).

prop(and(X,Y)):-
    prop(X),
    prop(Y).

prop(or(X,Y)):-
    prop(X),
    prop(Y).

prop(imp(X,Y)):-
    prop(X),
    prop(Y).

prop(neg(X)):-
    prop(X).

prop(cont).
