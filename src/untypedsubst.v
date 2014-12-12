Require Import utility.
Require Import PredomAux.
Require Import PredomSum. 
Require Import untypedlambda.
Require Import untypeddensem.

Set Implicit Arguments.
Unset Strict Implicit.

(* Need this for nice pretty-printing *)
Unset Printing Implicit Defensive.

(*==========================================================================
  Semantics of substitution and renaming
  ==========================================================================*)

(* Apply semantic function pointwise to a renaming or substitution *)
Fixpoint SemSubst env env' : Subst env' env -> SemEnv env -c> SemEnv env' := 
  match env' with
  | O => fun s => K _ (tt : DOne) 
  | S _ => fun s => <| SemSubst (tlMap s) , SemVal (hdMap s) |>
  end.

Fixpoint SemRenaming env env' : Renaming env' env -> SemEnv env -c> SemEnv env' := 
  match env' with
  | O  => fun s => K _ (tt : DOne)
  | S _ => fun s => <| SemRenaming (tlMap s) , SemVar (hdMap s) |>
  end.

Lemma SemLiftRenaming : 
  forall env env' (r : Renaming env env'), SemRenaming (tlMap (liftRenaming r)) == SemRenaming r << FST. 
Proof.
induction env. intros. simpl.
apply (DOne_final (K (Dprod (SemEnv env') VInf) (tt:DOne)) _).  

intros. 
simpl. destruct (consMapInv r) as [r' [var eq]]. 
subst. simpl. rewrite hdConsMap. rewrite tlConsMap.
specialize (IHenv env' r').
rewrite PROD_fun_comp. rewrite IHenv. auto. 
Qed.

(*==========================================================================
  Semantic function commutes with renaming
  ==========================================================================*)

Implicit Arguments uncurry.
Add Parametric Morphism (D E F:cpo) : (@SUM_fun D E F)
with signature (@Oeq (D -c> F)) ==> (@Oeq (E -c> F)) ==> (@Oeq (Dsum D E -c> F))
as SUM_fun_eq_compat.
intros f0 f1 feq g0 g1 geq.
refine (fcont_eq_intro _).
intro d. case d. intro dl. rewrite SUM_fun_simpl. rewrite SUM_fun_simpl. simpl. auto. 
intro dr. rewrite SUM_fun_simpl. rewrite SUM_fun_simpl. simpl. auto. 
Qed.


Lemma SemCommutesWithRenaming:
   (forall env (v : Value env) env' (r : Renaming env env'),
   SemVal v << SemRenaming r == SemVal (renameVal r v))
/\ (forall env (exp : Exp env) env' (r : Renaming env env'),
   SemExp exp << SemRenaming r == SemExp (renameExp r exp)).
Proof.
apply ExpValue_ind.

(* VAR *)
intros env var env' r.
simpl. 
induction var. 
simpl. rewrite SND_PROD_fun.
destruct (consMapInv r) as [r' [v eq]]. subst.
simpl. rewrite hdConsMap. trivial.
destruct (consMapInv r) as [r' [v eq]]. subst.
simpl. 
specialize (IHvar r').
rewrite <- IHvar. rewrite fcont_comp_assoc. 
rewrite tlConsMap. rewrite FST_PROD_fun. trivial.

(* TNUM *)
intros. simpl. rewrite fcont_comp_assoc. rewrite <- K_com; trivial.  


(* LAMBDA *)
intros E body IH E' s. 
specialize (IH _ (liftRenaming s)).
rewrite renameLAMBDA.
simpl SemVal. 
rewrite fcont_comp_assoc. rewrite fcont_comp_assoc. rewrite fcont_comp_assoc. rewrite fcont_comp_assoc.
rewrite Curry_comp. rewrite fcont_comp_assoc.
rewrite <- IH. rewrite PROD_map_fun. rewrite ID_comp_left. rewrite <- SemLiftRenaming. auto. 

(* OP *)
intros env n v1 IH1 v2 IH2 env' s. rewrite renameOP. simpl.
repeat (rewrite fcont_comp_assoc). rewrite <- IH1. rewrite <- IH2.
Implicit Arguments INR [D1 D2]. Implicit Arguments INL [D1 D2]. Implicit Arguments uncurry [D E F].
rewrite PROD_fun_compr. rewrite PROD_fun_compr. 
refine (fcont_comp_eq_compat _ _). 
admit.

(* IFZ *)
intros env v IH e1 IH1 e2 IH2 env' s. rewrite renameIFZ. simpl. 
repeat (rewrite fcont_comp_assoc). rewrite PROD_fun_compl. 
rewrite (PROD_fun_eq_compat (fcont_comp_assoc _ _ _) (Oeq_refl _)).
rewrite (PROD_fun_eq_compat (fcont_comp_eq_compat (Oeq_refl _) (IH _ _) ) (Oeq_refl _)).
rewrite (PROD_fun_eq_compat (Oeq_refl _) (fcont_comp_unitL _)).
rewrite <- (PROD_fun_eq_compat (Oeq_refl _) (fcont_comp_unitR _)).

Lemma xx D E F G (f:E -C-> F -C-> G) (h:D -C-> F) (g: E -C-> D) : 
          EV << PROD_fun f (h << g) == 
   EV << PROD_fun (curry (uncurry _ _ _ f << SWAP << PROD_map h ID << SWAP)) g.
intros ; apply fcont_eq_intro ; auto.
Qed.

rewrite xx. refine (fcont_comp_eq_compat (Oeq_refl _) _).
refine (PROD_fun_eq_compat _ (Oeq_refl _)). apply Oeq_sym.
refine (curry_unique _). rewrite fcont_comp_assoc.
apply fcont_eq_intro.
intros d. repeat (rewrite fcont_comp_simpl). case d ; clear d. intros ds dn.
repeat (rewrite PROD_map_simpl). rewrite ID_simpl. simpl. repeat (rewrite ID_simpl). simpl.
repeat (rewrite EV_simpl).  repeat (rewrite fcont_comp_simpl).
rewrite SUM_fun_simpl.
unfold VInf.
admit.

(* VAL *)
intros env v IH env' s. rewrite renameVAL. simpl. rewrite fcont_comp_assoc. rewrite IH. auto. 

(* LET *)
intros env e2 IH2 e1 IH1 env' s. rewrite renameLET. simpl. 
repeat (rewrite fcont_comp_assoc).
rewrite <- IH2. clear IH2.
rewrite <- IH1. clear IH1. 
refine (fcont_comp_eq_compat _ _). trivial. simpl. 
rewrite SemLiftRenaming. 
rewrite PROD_fun_comp. 
refine (PROD_fun_eq_compat _ _).
(*simpl. 
rewrite Curry_comp. simpl. *)
rewrite PROD_map_fun. 
rewrite KLEISLIR_comp. 
rewrite ID_comp_left.
admit.  trivial.


(* APP *)
intros env v1 IH1 v2 IH2 env' s. rewrite renameAPP. simpl. 
rewrite fcont_comp_assoc. rewrite <- IH1. rewrite <- IH2.
rewrite PROD_fun_comp. trivial.
Qed.

Set Printing Implicit Defensive.

Lemma SemShiftRenaming : 
  forall env env' (r : Renaming env env'), SemRenaming (shiftRenaming r) == SemRenaming r << FST.
Proof.
induction env. intros. simpl.
apply (DOne_final (K (Dprod (SemEnv env') VInf) (tt:DOne)) _).

intros. 
simpl. destruct (consMapInv r) as [r' [var eq]]. 
subst. simpl. rewrite hdConsMap. rewrite tlConsMap.
specialize (IHenv env' r').
rewrite PROD_fun_comp. rewrite IHenv. auto. 
Qed.

Lemma SemIdRenaming : forall env, SemRenaming (idRenaming env) == ID.
Proof.
induction env.
simpl. 
apply (DOne_final (K DOne _) _).

rewrite idRenamingDef. simpl SemRenaming. rewrite tlConsMap. rewrite SemShiftRenaming.  
rewrite IHenv. rewrite ID_comp_left.
apply fcont_eq_intro. intros. destruct x.  auto. 
Qed.


Lemma SemShiftSubst : 
  forall env env' (s : Subst env env'), SemSubst (shiftSubst s) == SemSubst s << FST.
Proof.
induction env. intros. simpl.
apply (DOne_final (K (Dprod (SemEnv env') VInf) (tt:DOne)) _). 

intros. 
simpl. destruct (consMapInv s) as [s' [var eq]]. 
subst. simpl. rewrite hdConsMap. rewrite tlConsMap.
specialize (IHenv env' s').
rewrite PROD_fun_comp.
refine (PROD_fun_eq_compat _ _).  
rewrite IHenv. auto. unfold shiftSubst.
rewrite shiftConsMap. rewrite hdConsMap.
simpl. rewrite <- (proj1 SemCommutesWithRenaming).
refine (fcont_comp_eq_compat _ _). trivial.
(* Seems a bit round-about *)
assert ((fun t0 => SVAR t0) = tlMap (liftRenaming (idRenaming env'))).
rewrite LiftRenamingDef. rewrite tlConsMap. apply MapExtensional.   auto.
rewrite H.
rewrite SemLiftRenaming. rewrite SemIdRenaming. rewrite ID_comp_left. auto. 
Qed.


Lemma SemLiftSubst : 
  forall env env' (s : Subst env env'), SemSubst (tlMap (liftSubst s)) == SemSubst s << FST. 
Proof.
intros.
rewrite LiftSubstDef. rewrite tlConsMap. apply SemShiftSubst. 
Qed.

(*==========================================================================
  Semantic function commutes with substitution
  ==========================================================================*)


Lemma SemCommutesWithSubst:
   (forall env (v : Value env) env' (s : Subst env env'),
   SemVal v << SemSubst s == SemVal (substVal s v))
/\ (forall env (e : Exp env) env' (s : Subst env env'),
   SemExp e << SemSubst s == SemExp (substExp s e)).
Proof.
apply ExpVal_ind.

(* TINT *)
intros. simpl. rewrite <- K_com; trivial.  

(* TBOOL *)
intros. simpl. rewrite <- K_com; trivial.

(* TVAR *)
intros env ty var env' s.
simpl. 
unfold substVal. simpl travVal.
induction var. simpl.   rewrite SND_PROD_fun.
destruct (consMapInv s) as [s' [v eq]]. subst.
simpl. rewrite hdConsMap. trivial.
destruct (consMapInv s) as [s' [v eq]]. subst.
simpl. 
specialize (IHvar s').
rewrite <- IHvar. rewrite fcont_comp_assoc. 
rewrite tlConsMap. rewrite FST_PROD_fun. trivial.

(* TFIX *)
intros E t t1 body IH E' s. rewrite substTFIX. simpl. 
rewrite fcont_comp_assoc.
rewrite Curry_comp. rewrite Curry_comp. rewrite <- IH.
clear IH. simpl. rewrite PROD_map_fun. rewrite PROD_map_fun. rewrite ID_comp_left. rewrite ID_comp_left.
rewrite SemLift2Subst. rewrite fcont_comp_assoc. rewrite PROD_fun_comp. rewrite fcont_comp_assoc. trivial. 

(* TPAIR *)
intros E t1 t2 v1 IH1 v2 IH2 E' s. rewrite substTPAIR. simpl. 
rewrite <- IH1. rewrite <- IH2. rewrite PROD_fun_comp. trivial. 

(* TFST *)
intros E t1 t2 v IH E' s. rewrite substTFST. simpl. 
rewrite <- IH. repeat (rewrite fcont_comp_assoc). trivial. 

(* TSND *)
intros E t1 t2 v IH E' s. rewrite substTSND. simpl.
rewrite <- IH. repeat (rewrite fcont_comp_assoc). trivial.

(* TOP *)
intros E n v1 IH1 v2 IH2 E' s. rewrite substTOP. simpl. 
repeat (rewrite fcont_comp_assoc). rewrite <- IH1. rewrite <- IH2.
rewrite PROD_fun_comp. trivial.

(* TGT *)
intros E v1 IH1 v2 IH2 E' s. rewrite substTGT. simpl. 
repeat (rewrite fcont_comp_assoc). rewrite <- IH1. rewrite <- IH2.
rewrite PROD_fun_comp. trivial.

(* TVAL *)
intros E t v IH E' s. rewrite substTVAL. simpl. 
rewrite <- IH. rewrite fcont_comp_assoc. trivial.

(* TLET *)
intros E t1 t2 e2 IH2 e1 IH1 E' s. rewrite substTLET. simpl. 
rewrite fcont_comp_assoc.
specialize (IH2 _ s).
specialize (IH1 _ (liftSubst _ s)).
rewrite PROD_fun_comp.
rewrite KLEISLIR_comp.
rewrite <- IH2. clear IH2. rewrite <- IH1. clear IH1. simpl.
rewrite PROD_map_fun. rewrite ID_comp_left. rewrite ID_comp_left. rewrite SemLiftSubst.  trivial.

(* TAPP *)
intros E t1 t2 v1 IH1 v2 IH2 E' s. rewrite substTAPP. simpl. 
rewrite fcont_comp_assoc. rewrite <- IH1. rewrite <- IH2.
rewrite PROD_fun_comp. trivial.

(* TIF *)
intros E t ec IHc te1 IH1 te2 IH2 E' s. rewrite substTIF. simpl. 
rewrite fcont_comp3_comp.
rewrite <- IHc. rewrite <- IH1. rewrite <- IH2. trivial.
Qed.