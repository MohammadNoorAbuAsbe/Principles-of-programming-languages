/*
 * ****************
 * Printing result depth
 *
 * You can enlarge it, if needed.
 * ****************
 */
maximum_printing_depth(100).

:- current_prolog_flag(toplevel_print_options, A),
   (select(max_depth(_), A, B), ! ; A = B),
   maximum_printing_depth(MPD),
   set_prolog_flag(toplevel_print_options, [max_depth(MPD)|B]).

% Signature: unique(List, UniqueList, Dups)/3
% Purpose: succeeds if and only if UniqueList contains the same elements of List without duplicates (according to their order in List), and Dups contains the duplicates

unique(List, UniqueList, Dups) :-
    unique2(List, UniqueList, Dups, 0,[], []).


isEmptyList([]).
isEqual(A,B,1):- !,(A = B).
isEqual(A,_,0):- !,(A = A).

remover( _, [], []).
remover( R, [R|T], T).
remover( R, [H|T], [H|T2]) :- H \= R, remover( R, T, T2).

first([A|_], A).


getByIndex([X], 0, X, _).
getByIndex([H|_], 0, H, _).
getByIndex([_|T], I, E, 1) :- NewIndex is I-1, getByIndex(T, NewIndex, E, 1).
getByIndex(_, _, _, 0).

increasePos(POS,NEWPOS,1):- NEWPOS is POS+1.
increasePos(POS,NEWPOS,0):- NEWPOS is POS.

reverse([],Z,Z).
reverse([H|T],Z,Acc) :- reverse(T,Z,[H|Acc]).

member(E,[E|_],0).
member(_,[],1).
member(E,[_|R],YESorNO) :- member(E,R,YESorNO).

add(E,List,NewList,DupList,NewDup,1):- NewList = [E|List], NewDup = DupList.
add(E,List,NewList,DupList,NewDup,0):- NewList = List, NewDup = [E|DupList].

list_length([]     , 0 ).
list_length([_|Xs] , L ) :- list_length(Xs,N) , L is N+1 .

unique2([], UniqueList, Dups, _, CheckedList,DupList):-
    list_length(UniqueList,ULength),
    list_length(CheckedList,CLength),
    !,
    isEqual(ULength,CLength,1),
    reverse(DupList,REV,[]),
    !,
    isEqual(Dups,REV,1).


unique2(GivenList, UniqueList, Dups, POS,CheckedList,DupList):-
    first(GivenList,FirstElement),
    remover(FirstElement,GivenList,NewGivenList),
    member(FirstElement,CheckedList,YesOrNo),
    add(FirstElement,CheckedList,NewCheckedList,DupList,NewDup,YesOrNo),
    getByIndex(UniqueList, POS, IndexElement,YesOrNo),
    increasePos(POS,NEWPOS,YesOrNo),
    !,
    isEqual(FirstElement,IndexElement,YesOrNo),
	unique2(NewGivenList, UniqueList, Dups, NEWPOS,NewCheckedList,NewDup).