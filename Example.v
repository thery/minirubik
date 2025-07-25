(*
Require Import Int31 List BasicRubik Rubik31 Solver.
*)
From Stdlib Require Import PrimInt63 List.
Require Import BasicRubik Rubik63 Solver.

(* Just to compute the state *)
Time Compute solve init_state.

(* swapping two adjacent corners *)
Time Compute solve (State C2 C1 C3 C4 C5 C6 C7 O1 O1 O1 O1 O1 O1 O1).

(* swap two opposite corners *)
Time Compute solve (State C7 C2 C3 C4 C5 C6 C1 O1 O1 O1 O1 O1 O1 O1).

Time Compute solve (State C2 C5 C3 C1 C4 C6 C7 O2 O3 O1 O3 O2 O1 O1).

Time Compute solve (State C1 C2 C3 C5 C6 C7 C4 O1 O1 O1 O2 O3 O2 O3).

Time Compute solve (State C1 C3 C6 C4 C2 C5 C7 O1 O1 O1 O1 O1 O1 O1).

Time Compute solve (State C7 C6 C5 C4 C3 C2 C1 O1 O1 O1 O1 O1 O1 O1).

