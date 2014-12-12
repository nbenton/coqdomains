Require Import utility.
Require Import PredomCore.
Require Import PredomProd.
Require Import PredomLift.
Require Import PredomKleisli.

Set Implicit Arguments.
Unset Strict Implicit.

Open Scope O_scope. 

(*==========================================================================
  Morphisms, missing from Predom.v
  ==========================================================================*)

(*==========================================================================
  Some basic lemmas
  ==========================================================================*)

Lemma eta_injective :
  forall D E (f g:D -c> E), eta << f == eta << g -> f == g.
intros D E f g eq.
refine (fcont_eq_intro _).
intro x. refine (vinj _).
assert (H := fcont_eq_elim eq x). auto.
Qed.

