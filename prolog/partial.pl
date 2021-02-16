:- module(partial, []).

:- use_module(utilities).
:- use_module(reify_reflect).

partial_compute_goal(Goal) :-
    partial_compute_goal(Goal, [], Final_State).


partial_compute_goal
