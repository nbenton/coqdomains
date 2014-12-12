(*==========================================================================
  Definition of products and associated lemmas
  ==========================================================================*)
Require Import PredomCore.
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.


(*==========================================================================
  Domain-theoretic definition
  ==========================================================================*)


Lemma curry_uncurry (D0 D1 D2:cpoType) : @CURRY D0 D1 D2 << uncurry =o= Id.
intros D0 D1 D2.
refine (fcont_eq_intro _). intros f. refine (fcont_eq_intro _). intros x. refine (fcont_eq_intro _). intros y. by auto.

(*
assert (forall D0 D1 D2 D3 D4 (f:D0 -c> D1) (g:D1 -C-> D2) (h:D3 -c> D4), (g << f) *f* h == (g *f* ID) << (f *f* h)).
intros. refine (Dprod_unique _ _) ; unfold PROD_map. rewrite FST_PROD_fun.
rewrite <- fcont_comp_assoc. rewrite FST_PROD_fun. repeat (rewrite fcont_comp_assoc). rewrite FST_PROD_fun. auto.
rewrite SND_PROD_fun.
rewrite <- fcont_comp_assoc. rewrite SND_PROD_fun. repeat (rewrite fcont_comp_assoc). rewrite SND_PROD_fun.
rewrite fcont_comp_unitL. auto.

apply Dext. rewrite H.
rewrite <- fcont_comp_assoc.
unfold CURRY. rewrite <- curry_com.
apply Dext.
rewrite H.
rewrite <- fcont_comp_assoc.
rewrite <- curry_com.
unfold uncurry.
rewrite fcont_comp_assoc.
assert ((<| FST << FST, <| SND << FST, SND |> |> <<
    (curry (D1:=D0 -C-> D1 -C-> D2) (D2:=D0 *c* D1) (D3:=D2)
       (EV << <| EV << <| FST, FST << SND |>, SND << SND |>) *f* 
     @ID D0) *f* @ID D1) == 
  (curry (EV << <| EV << <| FST, FST << SND |>, SND << SND |>) *f* (ID *f* ID)) <<
    <| FST << FST, <| SND << FST, SND |> |>).
refine (Dprod_unique _ _) ; unfold PROD_map.
rewrite <- fcont_comp_assoc. rewrite FST_PROD_fun. rewrite fcont_comp_assoc.
rewrite FST_PROD_fun. rewrite <- fcont_comp_assoc. rewrite FST_PROD_fun.
rewrite <- fcont_comp_assoc. rewrite FST_PROD_fun. repeat (rewrite fcont_comp_assoc). rewrite FST_PROD_fun. auto.
rewrite <- fcont_comp_assoc. rewrite SND_PROD_fun.
rewrite <- fcont_comp_assoc. rewrite SND_PROD_fun.
refine (Dprod_unique _ _). rewrite <- fcont_comp_assoc. rewrite FST_PROD_fun.
rewrite fcont_comp_assoc. rewrite FST_PROD_fun. rewrite <- fcont_comp_assoc. rewrite SND_PROD_fun.
repeat (rewrite <- fcont_comp_assoc). rewrite FST_PROD_fun.
repeat (rewrite fcont_comp_unitL).
repeat (rewrite fcont_comp_assoc). rewrite SND_PROD_fun. rewrite FST_PROD_fun. auto.
rewrite <- fcont_comp_assoc. repeat (rewrite SND_PROD_fun).
repeat (rewrite <- fcont_comp_assoc). rewrite SND_PROD_fun. rewrite fcont_comp_assoc.
rewrite SND_PROD_fun. rewrite fcont_comp_assoc.
rewrite SND_PROD_fun. auto.
rewrite H0. clear H0. rewrite <- fcont_comp_assoc.
assert (@ID D0 *f* @ID D1 == ID) as Ide. refine (Dprod_unique _ _) ; unfold PROD_map.
rewrite FST_PROD_fun. rewrite fcont_comp_unitR. rewrite fcont_comp_unitL. auto.
rewrite SND_PROD_fun. rewrite fcont_comp_unitR. rewrite fcont_comp_unitL. auto.
rewrite (PROD_map_eq_compat (Oeq_refl _) Ide). rewrite <- curry_com.
repeat (rewrite fcont_comp_assoc).
refine (fcont_comp_eq_compat (Oeq_refl _) _).
refine (Dprod_unique _ _) ; unfold PROD_map.
rewrite <- fcont_comp_assoc. repeat (rewrite FST_PROD_fun).
repeat (rewrite fcont_comp_assoc).
refine (fcont_comp_eq_compat (Oeq_refl _) _).
refine (Dprod_unique _ _). repeat (rewrite <- fcont_comp_assoc). repeat (rewrite FST_PROD_fun).
rewrite fcont_comp_unitL. auto. repeat (rewrite <- fcont_comp_assoc). repeat (rewrite SND_PROD_fun).
rewrite fcont_comp_unitL. rewrite fcont_comp_assoc. rewrite SND_PROD_fun. rewrite FST_PROD_fun. auto.
repeat (rewrite <- fcont_comp_assoc). repeat (rewrite SND_PROD_fun).
rewrite fcont_comp_assoc. repeat (rewrite SND_PROD_fun). rewrite fcont_comp_unitL. auto.*)
Qed.

(*
Lemma uncurry_curry (D0 D1 D2:cpo) : uncurry << @CURRY D0 D1 D2 == ID.
intros.
apply Dext. unfold uncurry.
assert (forall D0 D1 D2 D3 D4 (f:D0 -c> D1) (g:D1 -C-> D2) (h:D3 -c> D4), (g << f) *f* h == (g *f* ID) << (f *f* h)).
intros. refine (Dprod_unique _ _) ; unfold PROD_map. rewrite FST_PROD_fun.
rewrite <- fcont_comp_assoc. rewrite FST_PROD_fun. repeat (rewrite fcont_comp_assoc). rewrite FST_PROD_fun. auto.
rewrite SND_PROD_fun.
rewrite <- fcont_comp_assoc. rewrite SND_PROD_fun. repeat (rewrite fcont_comp_assoc). rewrite SND_PROD_fun.
rewrite fcont_comp_unitL. auto.

rewrite H. rewrite <- fcont_comp_assoc. rewrite <- curry_com. unfold CURRY.

*)


(** ** Indexed product of cpo's *)

(* Stuff
(** *** Particular cases with one or two elements *)

Section Product2.

Definition I2 := bool.
Variable DI2 : bool -> cpo.

Definition DP1 := DI2 true.
Definition DP2 := DI2 false.

Definition PI1 : Dprodi DI2 -c> DP1 := PROJ DI2 true.
Definition pi1 (d:Dprodi DI2) := PI1 d.

Definition PI2 : Dprodi DI2 -c> DP2 := PROJ DI2 false.
Definition pi2 (d:Dprodi DI2) := PI2 d.

Definition pair2 (d1:DP1) (d2:DP2) : Dprodi DI2 := bool_rect DI2 d1 d2.

Lemma pair2_le_compat : forall (d1 d'1:DP1) (d2 d'2:DP2), d1 <= d'1 -> d2 <= d'2 
            -> pair2 d1 d2 <= pair2 d'1 d'2.
intros; intro b; case b; simpl; auto.
Save.

Definition Pair2 : DP1 -m> DP2 -m> Dprodi DI2 := le_compat2_mon pair2_le_compat.

Definition PAIR2 : DP1 -c> DP2 -C-> Dprodi DI2.
apply continuous2_cont with (f:=Pair2).
red; intros; intro b.
case b; simpl; apply lub_le_compat; auto.
Defined.

Lemma PAIR2_simpl : forall (d1:DP1) (d2:DP2), PAIR2 d1 d2 = Pair2 d1 d2.
trivial.
Save.

Lemma Pair2_simpl : forall (d1:DP1) (d2:DP2), Pair2 d1 d2 = pair2 d1 d2.
trivial.
Save.

Lemma pi1_simpl : forall  (d1: DP1) (d2:DP2), pi1 (pair2 d1 d2) = d1.
trivial.
Save.

Lemma pi2_simpl : forall  (d1: DP1) (d2:DP2), pi2 (pair2 d1 d2) = d2.
trivial.
Save.

Definition DI2_map (f1 : DP1 -c> DP1) (f2:DP2 -c> DP2) 
               : Dprodi DI2 -c> Dprodi DI2 :=
                 DMAPi (bool_rect (fun b:bool => DI2 b -c>DI2 b) f1 f2).

Lemma Dl2_map_eq : forall (f1 : DP1 -c> DP1) (f2:DP2 -c> DP2) (d:Dprodi DI2),
               DI2_map f1 f2 d == pair2 (f1 (pi1 d)) (f2 (pi2 d)).
intros; simpl; apply Oprodi_eq_intro; intro b; case b; trivial.
Save.
End Product2.
Hint Resolve Dl2_map_eq.

Section Product1.
Definition I1 := unit.
Variable D : cpo.

Definition DI1 (_:unit) := D.
Definition PI : Dprodi DI1 -c> D := PROJ DI1 tt.
Definition pi (d:Dprodi DI1) := PI d.

Definition pair1 (d:D) : Dprodi DI1 := unit_rect DI1 d.

Definition pair1_simpl : forall (d:D) (x:unit), pair1 d x = d.
destruct x; trivial.
Defined.

Definition Pair1 : D -m> Dprodi DI1.
exists pair1; red; intros; intro d.
repeat (rewrite pair1_simpl);trivial.
Defined.


Lemma Pair1_simpl : forall (d:D), Pair1 d = pair1 d.
trivial.
Save.

Definition PAIR1 : D -c> Dprodi DI1.
exists Pair1; red; intros; repeat (rewrite Pair1_simpl).
intro d; rewrite pair1_simpl.
rewrite (Dprodi_lub_simpl (Di:=DI1)).
apply lub_le_compat; intros.
intro x; simpl; rewrite pair1_simpl; auto.
Defined.

Lemma pi_simpl : forall  (d:D), pi (pair1 d) = d.
trivial.
Save.

Definition DI1_map (f : D -c> D) 
               : Dprodi DI1 -c> Dprodi DI1 :=
                 DMAPi (fun t:unit => f).

Lemma DI1_map_eq : forall (f : D -c> D) (d:Dprodi DI1),
               DI1_map f d == pair1 (f (pi d)).
intros; simpl; apply Oprodi_eq_intro; intro b; case b; trivial.
Save.
End Product1.

Hint Resolve DI1_map_eq.
End of Stuff *)
