:- module(utilites, [
              xfy_list/3,
              mapm/5,
              type_assert/1
          ]).

/*
 * xfy_list(Op, Term, List) is det.
 *
 * Folds a functor over a list.
 */
xfy_list(Op, Term, [Left|List]) :-
    Term =.. [Op, Left, Right],
    xfy_list(Op, Right, List),
    !.
xfy_list(_, Term, [Term]).

/*
 * mapm(+P, +L1, +L2, +State1, -State2) is det.
 *
 * Monadic (double) map
 */
:- meta_predicate mapm(4,?,?,?,?).
mapm(P,L1,L2,S0,SN) :-
    mapm_(L1,L2,S0,SN,P).

mapm_([],[],S,S,_P).
mapm_([H|T],[HP|TP],S0,SN,P) :-
    call(P,H,HP,S0,S1),
    mapm_(T,TP,S1,SN,P).

:- meta_predicate type_assert(0).
type_assert(Goal) :-
    (   call(Goal)
    ->  true
    ;   throw(error(type_error, Goal))
    ).
