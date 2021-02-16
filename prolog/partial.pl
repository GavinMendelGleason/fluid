:- module(partial, [partial_compute_goal]).

:- use_module(utilities).
:- use_module(reify_reflect).
:- use_module(dict_state).

partial_compute_goal(Goal,Program) :-
    State = _{
                program: Program,
                choices: [],
                environment: []
            },
    partial_compute_goal(Goal,State,Final_State),
    writeq(Final_State).

partial_compute_goal(P,Q) -->
    partial_compute_goal(P),
    partial_compute_goal(Q).
partial_compute_goal(P;Q) -->
    push_continuation(goal(Q)),
    partial_compute_goal(P).
partial_compute_goal(!) -->
    pop_continuation.
partial_compute_goal(functor(Symbol/N,Args)) -->
    predicate_program(Symbol, N, Program),
    Program = [clause(Symbol/N, Head, Goal)|Rest],
    push_continuation(Rest),
    mapm(unify, Head, Args),
    partial_compute_goal(Goal).
