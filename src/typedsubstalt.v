Require Import utility.
Require Import PredomAux.
Require Import typedlambda.
Require Import typeddensem.
Require Import Program.Equality.

Set Implicit Arguments.
Unset Strict Implicit.

(* Need this for nice pretty-printing *)
Unset Printing Implicit Defensive.

(*==========================================================================
  Semantics of substitution and renaming
  ==========================================================================*)

Fixpoint SemMap (P:Env -> Ty -> Type) (sem : forall env ty, P env ty -> SemEnv env -c> SemTy ty) env env' : Map P env' env -> SemEnv env -c> SemEnv env' :=
  match env' return Map P env' env -> SemEnv env -c> SemEnv env' with
  | nil => fun s => K _ (tt:DOne)
  | _ => fun s => PROD_fun (SemMap sem (tlMap s)) (sem _ _ (hdMap s))
  end.

Definition semWk P (k:Kit P) (sem:forall E t, P E t -> SemEnv E -c> SemTy t) := forall E t0 t (v:P E t), sem _ _ (wk k t0 v) == sem E t v @_ FST.
Definition semVr P (k:Kit P) (sem:forall E t, P E t -> SemEnv E -c> SemTy t) := forall E t0, sem _ _ (vr k (ZVAR E t0)) == SND.
Definition semVl P (k:Kit P) (sem:forall E t, P E t -> SemEnv E -c> SemTy t) := forall E t (v:P E t), sem _ _ v = SemVal (vl k v).

Lemma SemShiftMap : 
  forall P (k:Kit P) sem, semWk k sem -> forall E E' (s:Map P E E') t, SemMap sem (shiftMap (K:=k) t s) == SemMap sem s @_ FST.
Proof.
intros P k sem semwk.
induction E. intros. simpl.
apply (DOne_final (K (Dprod (SemEnv E') (SemTy t)) (tt:DOne)) _). 

intros. 
simpl. destruct (consMapInv s) as [s' [var eq]]. 
subst. simpl. rewrite hdConsMap. rewrite tlConsMap.
specialize (IHE E' s' t).
rewrite PROD_fun_comp.
refine (PROD_fun_eq_compat _ _).  
rewrite IHE. auto.

rewrite shiftConsMap. rewrite hdConsMap.
unfold semWk in semwk.
rewrite semwk. auto. 
Qed.

Lemma SemLiftMap : 
  forall P (k:Kit P) sem, semWk k sem -> forall E E' (s:forall t, Var E t -> P E' t) t0, SemMap sem (tlMap (lift (K:=k) t0 s)) == SemMap sem s @_ FST. 
Proof.
induction E. intros. simpl.
apply (DOne_final (K (Dprod (SemEnv E') (SemTy t0)) (tt:DOne)) _).  

intros. 
simpl. destruct (consMapInv s) as [s' [var eq]]. 
subst. rewrite hdConsMap. rewrite tlConsMap.
specialize (IHE E' s' t0).
rewrite PROD_fun_comp.
refine (PROD_fun_eq_compat _ _).  
rewrite IHE. auto.unfold tlMap. simpl. unfold hdMap. simpl. 
unfold semWk in H. rewrite H. auto. 
Qed.

Lemma SemLift2Map : 
  forall P (k:Kit P) sem, semWk k sem -> forall E E' (s:Map P E E') t t', SemMap sem (tlMap (tlMap (lift (K:=k) t' (lift (K:=k) t s)))) == SemMap sem s @_ FST @_ FST. 
Proof.
induction E. intros. simpl.
apply (DOne_final (K (Dprod (Dprod (SemEnv E') (SemTy t)) (SemTy t')) (tt:DOne)) _). 

intros. 
simpl. destruct (consMapInv s) as [s' [var eq]]. 
subst. simpl. rewrite hdConsMap. rewrite tlConsMap.
specialize (IHE E' s' t).
rewrite PROD_fun_comp. rewrite PROD_fun_comp. 
refine (PROD_fun_eq_compat _ _).  
rewrite IHE. auto. unfold semWk in H. unfold hdMap. unfold tlMap.  simpl. rewrite H. rewrite H.  auto. 
Qed.


Lemma SemCommutesWithMap : forall P (k:Kit P) sem, semWk k sem -> semVr k sem -> semVl k sem -> 
   (forall E t (v : Value E t) E' (r : Map P E E'),
   SemVal v @_ SemMap sem r == SemVal (travVal v k r))
/\ (forall E t (exp : Exp E t) E' (r : Map P E E'),
   SemExp exp @_ SemMap sem r == SemExp (travExp exp k r)).
Proof.
intros P k sem semwk semvr semvl. unfold semWk in semwk. unfold semVr in semvr. unfold semVl in semvl.
apply ExpVal_ind.

(* TINT *)
intros. simpl. rewrite <- K_com; trivial.  

(* TBOOL *)
intros. simpl. rewrite <- K_com; trivial.

(* TVAR *)
intros E t var E' s.
simpl. 
dependent induction var. simpl. rewrite SND_PROD_fun.
destruct (consMapInv s) as [s' [v eq]]. subst.
simpl. rewrite hdConsMap. rewrite semvl. trivial.
destruct (consMapInv s) as [s' [v eq]]. subst.
simpl. 
specialize (IHvar s' var (JMeq_refl _)).
rewrite <- IHvar. rewrite fcont_comp_assoc. 
rewrite tlConsMap. rewrite FST_PROD_fun. trivial.

(* TFIX *)
intros E t t1 body IH E' s. 
specialize (IH (t :: t --> t1 :: E') (lift (K:=k) t (lift (K:=k) (t --> t1) s))).
simpl SemVal. 
rewrite fcont_comp_assoc. rewrite Curry_comp. rewrite Curry_comp. rewrite <- IH.
clear IH. simpl. rewrite PROD_map_fun. rewrite PROD_map_fun. rewrite ID_comp_left. rewrite ID_comp_left.
rewrite PROD_fun_comp. rewrite SemLift2Map. unfold tlMap. unfold hdMap. simpl. 
rewrite semvr. rewrite semwk. rewrite semvr. auto. auto. 

(* TPAIR *)
intros E t1 t2 v1 IH1 v2 IH2 E' s.
simpl SemVal. rewrite <- IH1. rewrite <- IH2. rewrite <- PROD_fun_comp. trivial. 

(* TFST *)
intros E t1 t2 v IH E' s. simpl SemExp. 
rewrite <- IH. repeat (rewrite fcont_comp_assoc). trivial. 

(* TSND *)
intros E t1 t2 v IH E' s. simpl SemExp.
rewrite <- IH. repeat (rewrite fcont_comp_assoc). trivial.

(* TOP *)
intros E n v1 IH1 v2 IH2 E' s. simpl SemExp. 
repeat (rewrite fcont_comp_assoc). rewrite <- IH1. rewrite <- IH2.
rewrite PROD_fun_comp. trivial.

(* TGT *)
intros E v1 IH1 v2 IH2 E' s. simpl SemExp.
repeat (rewrite fcont_comp_assoc). rewrite <- IH1. rewrite <- IH2.
rewrite PROD_fun_comp. trivial.

(* TVAL *)
intros E t v IH E' s. simpl SemExp. 
rewrite <- IH. rewrite fcont_comp_assoc. trivial.

(* TLET *)
intros E t1 t2 e2 IH2 e1 IH1 E' s. simpl SemExp. 
rewrite fcont_comp_assoc.
specialize (IH2 _ s).
specialize (IH1 _ (lift (K:=k) _ s)).
rewrite PROD_fun_comp.
rewrite KLEISLIR_comp.
rewrite <- IH2. clear IH2. rewrite <- IH1. clear IH1. simpl. 
rewrite PROD_map_fun. rewrite ID_comp_left. rewrite ID_comp_left. 
rewrite SemLiftMap. unfold hdMap. simpl. rewrite semvr. trivial. trivial. 

(* TAPP *)
intros E t1 t2 v1 IH1 v2 IH2 E' s. simpl SemExp. 
rewrite fcont_comp_assoc. rewrite <- IH1. rewrite <- IH2.
rewrite PROD_fun_comp. trivial.

(* TIF *)
intros E t ec IHc te1 IH1 te2 IH2 E' s. simpl SemExp. 
rewrite fcont_comp3_comp. rewrite <- IHc. rewrite <- IH1. rewrite <- IH2. trivial.
Qed.

Definition SemRenaming := SemMap SemVar.
Definition SemSubst := SemMap SemVal.

Corollary SemCommutesWithRenaming:
   (forall E t (v : Value E t) E' (r : Renaming E E'),
   SemVal v @_ SemRenaming r == SemVal (renameVal r v))
/\ (forall E t (exp : Exp E t) E' (r : Renaming E E'),
   SemExp exp @_ SemRenaming r == SemExp (renameExp r exp)).
Proof.
assert (H1 : semWk RenamingKit SemVar). unfold semWk; intros;auto. 
assert (H2 : semVr RenamingKit SemVar). unfold semVr; auto. 
assert (H3 : semVl RenamingKit SemVar). unfold semVl; auto. 
assert (H := SemCommutesWithMap H1 H2 H3). auto.  
Qed.

(*==========================================================================
  Semantic function commutes with substitution
  ==========================================================================*)

Lemma SemIdRenaming : forall E, SemRenaming (idRenaming E) == ID.
Proof.
induction E.
simpl. 
apply (DOne_final (K DOne _) _).

rewrite idRenamingDef. unfold SemRenaming. unfold SemMap. rewrite tlConsMap. fold SemMap. simpl. unfold shiftRenaming. rewrite SemShiftMap.  
rewrite IHE. rewrite ID_comp_left.
apply fcont_eq_intro. intros. destruct x.  auto. unfold semWk. intros. auto. 
Qed.



Lemma SemRenamingShift : forall E t0, SemRenaming (fun s : Ty => SVAR (env:=E) t0) == FST.
induction E. 
intros t0. apply fcont_eq_intro. intros x.
case x.  intros. simpl in *. dependent destruction x. unfold SemRenaming. unfold SemMap. rewrite K_simpl. case t. auto. 

(* Seems a bit round-about *)
intros t0. 
assert ((fun s => SVAR t0) = tlMap (lift (K:=RenamingKit) t0 (idRenaming (a::E)))).
rewrite LiftRenamingDef. rewrite tlConsMap. apply MapExtensional. auto.
rewrite H. unfold SemRenaming.
rewrite SemLiftMap. rewrite SemIdRenaming. rewrite ID_comp_left. auto. 
unfold semWk. intros. auto. 
Qed.

Corollary SemCommutesWithSubst:
   (forall E t (v : Value E t) E' (s : Subst E E'),
   SemVal v @_ SemSubst s == SemVal (substVal s v))
/\ (forall E t (exp : Exp E t) E' (s : Subst E E'),
   SemExp exp @_ SemSubst s == SemExp (substExp s exp)).
Proof.
assert (H1 : semWk SubstKit SemVal). unfold semWk; intros.
simpl. rewrite <- (proj1 SemCommutesWithRenaming).
refine (fcont_comp_eq_compat _ _). trivial. rewrite SemRenamingShift. auto. 
assert (H2 : semVr SubstKit SemVal). unfold semVr; auto. 
assert (H3 : semVl SubstKit SemVal). unfold semVl; auto. 
assert (H := SemCommutesWithMap H1 H2 H3). unfold renameVal. unfold renameExp. 
split. intros. apply (proj1 H).  
intros. apply (proj2 H). 
Qed.

