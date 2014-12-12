(* untypedopsem.v
   Standard operational semantics 
*)
Require Import utility.
Require Import Coq.Program.Equality.
Require Import EqdepFacts. 
Require Import untypedlambda.

Set Implicit Arguments.
Unset Strict Implicit.

(*==========================================================================
  Evaluation relation
  ==========================================================================*)

(** printing =>> %\ensuremath{\Downarrow}% *)
(** printing n1 %\ensuremath{n_1}% *)
(** printing n2 %\ensuremath{n_2}% *)
(** printing v1 %\ensuremath{v_1}% *)
(** printing v2 %\ensuremath{v_2}% *)
(** printing e1 %\ensuremath{e_1}% *)
(** printing e2 %\ensuremath{e_2}% *)
Reserved Notation "e =>> v" (at level 70, no associativity). 

Open Scope Subst_scope.
Inductive Ev : CExp -> CValue -> Prop :=
| e_Val : forall v, VAL v =>> v
| e_App : forall e1 v2 v, substExp (consMap v2 (idSubst _)) e1 =>> v -> APP (LAMBDA e1) v2 =>> v
| e_Let : forall e1 v1 e2 v2, e1 =>> v1 -> substExp (consMap v1 (idSubst _)) e2 =>> v2 -> (LET e1 e2) =>> v2
| e_IfzTrue : forall e1 e2 v1, e1 =>> v1 -> IFZ (NUM 0) e1 e2 =>> v1
| e_IfzFalse : forall e1 e2 v2 n, e2 =>> v2 -> IFZ (NUM (S n)) e1 e2 =>> v2
| e_Op : forall op n1 n2, OP op (NUM n1) (NUM n2) =>> NUM (op n1 n2)
where "e =>> v" := (Ev e v).
