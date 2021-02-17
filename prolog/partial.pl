:- module(partial, [
              goal_program_state/3,
              partial_compute_goal/3
          ]).

:- use_module(utilities).
:- use_module(reify_reflect).
:- use_module(dict_state).

goal_program_state(Goal,Program,Final_State) :-
    State = state{
                program: Program,
                continuation: [],
                environment: []
            },
    compute_goal(Goal,State,Final_State),
    writeq(Final_State).

push_continuation(List) -->
    update(continuation, Old, New),
    { append(List, Old, New) }.

suffix([],[]).
suffix([goal(_)|Rest], Rest).
suffix([continuation(_,_,_)|Rest], Rest).

cut_continuations -->
    update(continuation, Old, New),
    { suffix(Old,New) }.

pop_continuations(Continuation -->
    update(continuation, [, New).

predicate_clauses(Symbol, N, Clauses) -->
    view(program, Program),
    { findall(clause(Symbol/N,Args,Goals),
              member(clause(Symbol/N,Args,Goals), Program),
              Clauses)
    }.


%! try_compute_goal(G:goal,S0:state,S1:state) is semidet.
%
% Try to compute the outcome of a 

try_compute_goal(G) -->
    true.

compute_goal((P,Q)) -->
    compute_goal(P),
    compute_goal(Q).
compute_goal((P;Q)) -->
    push_continuation([goal(Q)]),
    compute_goal(P).
compute_goal(!) -->
    cut_continuations.
compute_goal(functor(Symbol/N,Args)) -->
    predicate_clauses(Symbol, N, [clause(Symbol/N, Head, Goal)|Rest]),
    push_continuation(continuation(Args,Rest)),
    compute_args_head_goal(Args,Head,Goal),
compute_goal(_) -->
    pop_continuation(functor(Symbol/N,Args),clause(Symbol/N, Head, Goal)),
    compute_args_head_goal(Args,Head,Goal).

compute_args_head_goal(Args,Head,Goal) -->
    mapm(unify, Head, Args),
    compute_goal(Goal).

:- begin_tests(partial).

test(plus, []) :-
    Pre_Program = [
        plus(z,Y,Y),
        plus(s(X), Y, s(Z)) :-
            plus(X, Y, Z)],

    maplist(reify_reflect, Pre_Program, Program),
    fix_vars(Program),

    Pre_Goal = plus(z,s(z), _),
    reify_reflect_goal(Pre_Goal,Goal),
    fix_vars(Goal),

    goal_program_state(Goal,Program,State),

    writeq(State).

:- end_tests(partial).
