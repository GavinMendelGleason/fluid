:- module(reify_reflect, [
              reify_reflect/2,
              reify_reflect_goal/2,
              free/2,
              bound/2,
              fix_vars/1,
              unfix_vars//2,
              unify//2
          ]).

:- use_module(utilities).
:- use_module(dict_state).

/*
 * reify_reflect(+,-) is det.
 * reify_reflect(-,+) is det.
 */
reify_reflect((:- Body),declaration(Clauses)) :-
    !,
    xfy_list(',', Body, Clauses).
reify_reflect((Head --> Body),clause(P//N,RArgs,Clauses)) :-
    Head =.. [P|Args],
    length(Args,N),
    maplist(reify_reflect_term,Args,RArgs),
    xfy_list(',', Body, Clauses),
    !.
reify_reflect((Head :- Body),clause(P/N,RArgs,[RClause|RClauses])) :-
    Head =.. [P|Args],
    length(Args,N),
    maplist(reify_reflect_term,Args,RArgs),
    xfy_list(',', Body, [Clause|Clauses]),
    maplist(reify_reflect_goal,[Clause|Clauses],[RClause|RClauses]),
    !.
reify_reflect(Head,clause(P/N,RArgs,[])) :-
    Head =.. [P|Args],
    length(Args,N),
    maplist(reify_reflect_term,Args,RArgs).

% reify_reflect_goal allows us to take a prolog term and give it a
% unambiguous representation.
/*
 * reify_reflect_goal(+,-) is det.
 * reify_reflect_goal(-,+) is det.
 */
reify_reflect_term(X, var(X)) :-
    var(X),
    !.
reify_reflect_term(X, integer(X)) :-
    integer(X),
    !.
reify_reflect_term(X, float(X)) :-
    float(X),
    !.
reify_reflect_term(Functor, lambda(Free,Bound,Goal)) :-
    when((   nonvar(Functor)
         ;   nonvar(F)),
         Functor =.. [F,Args,Goal]),
    member(F,['>>', '/']),
    free(Args, Free),
    bound(Args, Bound),
    !.
reify_reflect_term(Functor, functor(Symbol/N,Reflect_Args)) :-
    Functor =.. [Symbol|Reify_Args],
    length(Reify_Args,N),
    maplist(reify_reflect_term,Reify_Args,Reflect_Args).

reify_reflect_goal((!), cut) :-
    !.
reify_reflect_goal((A,B), (RA,RB)) :-
    !,
    reify_reflect_goal(A, RA),
    reify_reflect_goal(B, RB).
reify_reflect_goal((A,B), (RA,RB)) :-
    !,
    reify_reflect_goal(A, RA),
    reify_reflect_goal(B, RB).
reify_reflect_goal(Functor, call(RGoal,Reflect_Args)) :-
    Functor =.. [call,Goal|Reify_Args],
    !,
    reify_reflect_goal(Goal, RGoal),
    maplist(reify_reflect_term,Reify_Args,Reflect_Args).
reify_reflect_goal(Functor, functor(Symbol/N,Reflect_Args)) :-
    Functor =.. [Symbol|Reify_Args],
    % \+ member(Symbol, [!,',',';', 'call']),
    length(Reify_Args,N),
    maplist(reify_reflect_term,Reify_Args,Reflect_Args).

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
                Var = X
            ), Variables).

% needs to walk the entire syntax.
unfix_vars(integer(X),integer(X)) --> [].
unfix_vars(float(X),float(X)) --> [].
unfix_vars(functor(F,L),float(F,M)) -->
    mapm(unfix_vars, L, M).
/*
unfix_vars(lambda(FreeX, BoundX, GoalX),lambda(FreeY, BoundY, GoalY)) -->
    {throw(error(unimplemented))}.
*/

:- begin_tests(reify_reflect).

test(plus_goal_reify,[]) :-
    Pre_Goal = plus(z,s(z), _),
    reify_reflect_goal(Pre_Goal,Goal),
    Goal = functor(plus/3,[functor(z/0,[]),
                           functor(s/1,[functor(z/0,[])]),
                           var(_)]).

test(plus_reify,[]) :-

    Pre_Program = [
        plus(z,Y,Y),
        plus(s(X), Y, s(Z)) :-
            plus(X, Y, Z)],

    maplist(reify_reflect, Pre_Program, Program),
    fix_vars(Program),
    Program = [clause(plus/3,[functor(z/0,[]),var(A),var(A)],[]),
               clause(plus/3,[functor(s/1,[var(E)]),var(F),functor(s/1,[var(G)])],
                      [functor(plus/3,[var(E),var(F),var(G)])])].


:- end_tests(reify_reflect).

extend(X, R) -->
    update(environment, Env, [X-R|Env]).

lookup(Y, R) -->
    view(environment, Env),
    { memberchk(Y-R, Env) }.

unify(var(X), var(Y)) -->
    (   lookup(Y,R)
    ->  (   lookup(X,S)
        ->  unify(R,S)
        ;   extend(X,R))
    ;   extend(X,var(Y))
    ).
unify(var(X), functor(P/N, L)) -->
    extend(X,functor(P/N, L)).
unify(functor(P/N, L), var(X)) -->
    unify(var(X), functor(P/N, L)).
unify(functor(P/N, L1), functor(P/N, L2)) -->
    mapm(unify, L1, L2).

:- begin_tests(unification).

test(var_var, []) :-
    unify(var(x),var(y), state{ environment : []}, State),
    !,
    lookup(x,var(y),State,_).

test(var_atom, []) :-
    unify(var(x),functor(z/0,[]), state{ environment : []}, State),
    !,
    lookup(x,functor(z/0,[]),State,_).

test(atom_var, []) :-
    unify(functor(z/0,[]), var(x), state{ environment : []}, State),
    !,
    lookup(x,functor(z/0,[]),State,_).

test(atom_atom, []) :-
    unify(functor(z/0,[]), functor(z/0,[]), state{ environment : []}, _State),
    !.

test(functor_functor, []) :-
    unify(functor(f/0,[var(x),functor(a/0,[])]),
          functor(f/0,[functor(b/0,[]),var(y)]),
          state{ environment : []}, State),
    !,
    lookup(x,functor(b/0,[]),State,_),
    lookup(y,functor(a/0,[]),State,_).

:- end_tests(unification).
