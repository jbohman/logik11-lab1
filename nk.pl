verify(InputFileName) :- 
    see(InputFileName),
    read(Prems), read(Goal), read(Proof),
    seen,
    valid_fwd(Prems, Goal, Proof).

valid_fwd(Prems, Goal, Proof):-
    reverse(Proof, RevProof), valid_rev(Prems, Goal, RevProof).

valid_rev(Prems, Goal, RevProof):-
    RevProof = [[_, Goal, X]|Rp], /* Goal at end of Proof */
    X \== assumption,
    flatten(RevProof, Frp),
    valid(Prems, RevProof, Frp).

valid(_,[],_).

% assumption
valid(Prems, [[_,_,assumption]|[]], Frp):-
    write('assumption').


% premise
valid(Prems, [[X,Y,premise]|Rest], Frp):-
    number(X),
    prop(Y),
    member(Y, Prems),
    write('premise'),
    valid(Prems, Rest, Frp).


% copy(x)
valid(Prems, [[X,Y,Z]|Rest], Frp):-
    number(X),
    prop(Y),
    Z = copy(A),
    member([A,Y,_], Frp),
    write('copy(x)'),
    valid(Prems, Rest, Frp).


% andint(x,y)
valid(Prems, [[X,Y,Z]|Rest], Frp):-
    number(X),
    prop(Y),
    Z = andint(A,B),
    member([A, C, _], Frp),
    member([B, D, _], Frp),
    Y == and(C,D),
    write('andint(x,y)'),
    valid(Prems, Rest, Frp).

% andel1(x)
valid(Prems, [[X,Y,Z]|Rest], Frp):-
    number(X),
    prop(Y),
    Z = andel1(A),
    member([A, B, _], Frp),
    B = and(D, _),
    Y == D,
    write('andel1(x)'),
    valid(Prems, Rest, Frp).

% andel2(x)
valid(Prems, [[X,Y,Z]|Rest], Frp):-
    number(X),
    prop(Y),
    Z = andel2(A),
    member([A, B, _], Frp),
    B = and(_, E),
    Y == E,
    write('andel2(x)'),
    valid(Prems, Rest, Frp).


% orint1(x) TODO
%valid(Prems, [[X,Y,Z]|Rest], Frp):-
    %number(X),
    %prop(Y),
    %write('orint1(x)'),
    %valid(Prems, Rest, Frp).

% orint2(x) TODO
%valid(Prems, [[X,Y,Z]|Rest], Frp):-
    %number(X),
    %prop(Y),
    %write('orint2(x)'),
    %valid(Prems, Rest, Frp).

% orel(x,y,u,v,w)
valid(Prems, [[X,Y,Z]|Rest], Frp):-
    number(X),
    prop(Y),
    Z = orel(A,B,C,D,E),
    member([A, F, _], Frp),
    F = or(G,H),
    member([B, G, _], Frp),
    member([C, I, _], Frp),
    member([D, H, _], Frp),
    member([E, J, _], Frp),
    I == J,
    J == Y,
    write('orel checked'),
    valid(Prems, Rest, Frp).


% impint(x,y)
valid(Prems, [[X,Y,Z]|Rest], Frp):-
    number(X),
    prop(Y),
    Z = impint(A,B),
    Y = imp(C,D),
    member([A,C,_], Frp), /* TODO: check assumption elims */
    member([B,D,_], Frp),
    write('impint checked'),
    valid(Prems, Rest, Frp).

% impel(x,y)
valid(Prems, [[X,Y,Z]|Rest], Frp):-
    number(X),
    prop(Y),
    Z = impel(A,B),
    member([B, imp(F,Y), _], Frp),
    member([A, F, _], Frp),
    write('impel checked'),
    valid(Prems, Rest, Frp).


% negint(x,y)
valid(Prems, [[X,Y,Z]|Rest], Frp):-
    number(X),
    prop(Y),
    Y = neg(E),
    Z = negint(A,B),
    member([A, E, _], Frp),
    member([B, cont, _], Frp),
    write('negint checked'),
    valid(Prems, Rest, Frp).

% negel(x,y)
valid(Prems, [[X,Y,Z]|Rest], Frp):-
    number(X),
    prop(Y),
    Y = cont,
    Z = negel(A,B),
    member([A, C, _], Frp),
    member([B, D, _], Frp),
    D == neg(C),
    write('negel checked'),
    valid(Prems, Rest, Frp).


% contel(x) TODO
%valid(Prems, [[X,Y,Z]|Rest], Frp):-
    %number(X),
    %prop(Y),
    %write('contel(x)'),
    %valid(Prems, Rest, Frp).


% negnegint(x)
valid(Prems, [[X,Y,Z]|Rest], Frp):-
    number(X),
    prop(Y), % Y == neg(neg(_)) ?
    Z = negnegint(A),
    member([A, B, _], Frp),
    prop(B),
    write('negnegint(x)'),
    valid(Prems, Rest, Frp).

% negnegel(x)
valid(Prems, [[X,Y,Z]|Rest], Frp):-
    number(X),
    prop(Y),
    Z = negnegel(A),
    member([A, B, _], Frp),
    prop(B), % B == neg(neg(Y)) ?
    write('negnegel(x)'),
    valid(Prems, Rest, Frp).


% mt(x,y) TODO
%valid(Prems, [[X,Y,Z]|Rest], Frp):-
    %number(X),
    %prop(Y),
    %write('mt(x,y)'),
    %valid(Prems, Rest, Frp).


% pbc(x,y)
valid(Prems, [[X,Y,Z]|Rest], Frp):-
    number(X),
    prop(Y),
    Z = pbc(A,B),
    member([A, neg(Y), _], Frp),
    member([B, cont, _], Frp),
    write('pbc checked'),
    valid(Prems, Rest, Frp).



% box?? should be assumption?
valid(Prems, [Box|Rest], Frp):-
    write('found a box'),
    reverse(Box, RevBox),
    valid(Prems, RevBox, Frp),
    valid(Prems, Rest, Frp).

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
