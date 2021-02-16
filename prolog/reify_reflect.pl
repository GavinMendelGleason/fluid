:- module(reify_reflect, [
              reify_reflect/2,
              reify_reflect_goal/2,
              free/2,
              bound/2,
              fix_vars/1,
              unfix_vars/4,
              unify/3
          ]).

:- use_module(utilities).

/*
 * reify_reflect(+,-) is det.
 * reify_reflect(-,+) is det.
 */
reify_reflect((:- Body),declaration(Clauses)) :-
    !,
    xfy_list(',', Body, Clauses).
reify_reflect((Head --> Body),clause(P//N,Args,Clauses)) :-
    Head =.. [P|Args],
    length(Args,N),
    xfy_list(',', Body, Clauses),
    !.
reify_reflect((Head :- Body),clause(P/N,Args,[Clause|Clauses])) :-
    Head =.. [P|Args],
    length(Args,N),
    xfy_list(',', Body, [Clause|Clauses]),
    !.
reify_reflect(Head,clause(P/N,Args,[])) :-
    Head =.. [P|Args],
    length(Args,N).

% reify_reflect_goal allows us to take a prolog term and give it a
% unambiguous representation.
/*
 * reify_reflect_goal(+,-) is det.
 * reify_reflect_goal(-,+) is det.
 */
reify_reflect_goal(X, X) :-
    var(X),
    !.
reify_reflect_goal(X, integer(X)) :-
    integer(X),
    !.
reify_reflect_goal(X, float(X)) :-
    float(X),
    !.
reify_reflect_goal(Functor, lambda(Free,Bound,Goal)) :-
    when((   nonvar(Functor)
         ;   nonvar(F)),
         Functor =.. [F,Args,Goal]),
    member(F,['>>', '/']),
    free(Args, Free),
    bound(Args, Bound),
    !.
reify_reflect_goal(Functor, functor(Symbol/N,Reflect_Args)) :-
    Functor =.. [Symbol|Reify_Args],
    length(Reify_Args,N),
    maplist(reify_reflect_goal,Reify_Args,Reflect_Args).

free(_Bound, []).
free({Free}/[], [Free]) :-
    var(Free).
free({Free}/[], Vars) :-
    xfy_list(',', Free, Vars).
free({Free}/_Bound, [Free]) :-
    var(Free).
free({Free}/_Bound, Vars) :-
    xfy_list(',', Free, Vars).
free({Free}, [Free]) :-
    var(Free).
free({Free}, Vars) :-
    xfy_list(',', Free, Vars).

bound([], []).
bound([H|T], [H|T]).
bound({_Free}/[], []).
bound({_Free}/[H|T], [H|T]).
bound({_Free}, []).

fix_vars(Term) :-
    term_variables(Term, Variables),
    maplist([Var]>>(
                gensym('V', X),
                Var = var(X)
            ), Variables).

% needs to walk the entire syntax.
unfix_vars(integer(X),integer(X)) --> [].
unfix_vars(float(X),float(X)) --> [].
unfix_vars(functor(F,L),float(F,M)) -->
    mapm(unfix_vars, L, M).
unfix_vars(lambda(FreeX, BoundX, GoalX),lambda(FreeY, BoundY, GoalY)) -->
    {throw(error(unimplemented))}.

extend(X, R, Env, [v(X)-R|Env]).

lookup(Y, R, Env, Env) :-
    memberchk(v(Y)-R, Env).

unify(var(X), var(Y)) -->
    (   lookup(Y,R)
    ->  (   lookup(X,S)
        ->  unify(R,S)
        ;   extend(X,R))
    ;   extend(X,var(Y))
    ).
unify(functor(P/N, L), var(X)) -->
    unify(var(X), functor(P/N, L)).
unify(var(X), functor(P/N, L)) -->
    extend(X,functor(P/N, L)).
unify(functor(P/N, L1), functor(P/N, L2)) -->
    mapm(unify, L1, L2).
