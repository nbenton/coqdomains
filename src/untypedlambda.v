(*==========================================================================
  Call-by-value untyped lambda-calculus with arithmetic
  ==========================================================================*)

Require Import utility.
Require Import List.
Set Implicit Arguments.
Unset Strict Implicit.
Set Printing Implicit Defensive.

(** printing Env %{\textsf{Env}}% *)
(** printing env %{\ensuremath{\Gamma}}% *)
(** printing env' %{\ensuremath{\Gamma'}}% *)

Notation "[ x , .. , y ]" := (cons x .. (cons y nil) ..) : list_scope.

Require Import Coq.Program.Equality.

(*==========================================================================
  Typed terms in context
  ==========================================================================*)

Definition Env := nat.

(* Variables *)
Inductive Var : Env -> Type := 
| ZVAR : forall env, Var (S env)
| SVAR : forall env, Var env -> Var (S env).

(* Values (= canonical forms) *)
Inductive Value : Env -> Type :=
| VAR : forall env, Var env -> Value env
| NUM : forall env, nat -> Value env
| LAMBDA : forall env, Exp (S env) -> Value env

(* Expressions *)
with Exp : Env -> Type :=
| OP : forall env, (nat->nat->nat) -> Value env -> Value env -> Exp env
| IFZ : forall env, Value env -> Exp env -> Exp env -> Exp env
| VAL : forall env, Value env -> Exp env
| LET : forall env, Exp env -> Exp (S env) -> Exp env
| APP : forall env, Value env -> Value env -> Exp env.

Implicit Arguments NUM [env]. 
Scheme Value_rec2 := Induction for Value Sort Set
  with Exp_rec2 := Induction for Exp Sort Set.

Scheme Value_type2 := Induction for Value Sort Type
  with Exp_type2 := Induction for Exp Sort Type.

Scheme Value_ind2 := Induction for Value Sort Prop
  with Exp_ind2 := Induction for Exp Sort Prop.

Combined Scheme ExpValue_ind from Value_ind2, Exp_ind2.

(* Closed expressions and values *)
Definition CExp := Exp O.
Definition CValue := Value O.

(*==========================================================================
  Variable-domain maps. 
  By instantiating P with Var we get renamings.
  By instantiating P with Val we get substitutions.
  ==========================================================================*)

Definition Map (P:Env -> Type) env env' := Var env -> P env'.

(* Head, tail and cons *)
Definition tlMap P env env' (m:Map P (S env) env') : Map P env env' := fun v => m (SVAR v).
Definition hdMap P env env' (m:Map P (S env) env') : P env' := m (ZVAR _).
Implicit Arguments tlMap [P env env'].
Implicit Arguments hdMap [P env env'].

Program Definition consMap P env env' (v:P env') (m:Map P env env') : Map P (S env) env' :=
    fun (var:Var (S env)) => 
    match var with
    | ZVAR _ => v
    | SVAR _ var => m var
    end.
Implicit Arguments consMap [P env env'].

Axiom MapExtensional : forall P env env' (r1 r2 : Map P env env'), (forall var, r1 var = r2 var) -> r1 = r2.

Lemma hdConsMap : forall P env env' (v:P env') (s:Map P env env'), hdMap (consMap v s) = v. Proof. auto. Qed.
Lemma tlConsMap : forall P env env' (v:P env') (s:Map P env env'), tlMap (consMap v s) = s. Proof. intros. apply MapExtensional. auto. Qed.

Lemma consMapInv : forall P env env' (m:Map P (S env) env'), exists m', exists v, m = consMap v m'.  
intros. exists (tlMap m). exists (hdMap m).
apply MapExtensional. intros var. dependent destruction var; auto. 
Qed.

(*==========================================================================
  Package of operations used with a Map
    vr maps a Var into Var or Value (so is either the identity or TVAR)
    vl maps a Var or Value to a Value (so is either TVAR or the identity)
    wk weakens a Var or Value (so is either SVAR or renaming through SVAR on a value)
  ==========================================================================*)
Record MapOps (P : Env -> Type) :=
{
  vr : forall env, Var env -> P env;   
  vl : forall env, P env -> Value env;
  wk : forall env, P env -> P (S env) 
}.

Section MapOps.

  Variable P : Env -> Type.
  Variable ops : MapOps P.

  Program Definition lift env env' (m : Map P env env') : Map P (S env) (S env') :=
  fun var => match var with
  | ZVAR _ => vr ops (ZVAR _)
  | SVAR _ x => wk ops (m x)
  end.
  Implicit Arguments lift [env env'].

  Definition shiftMap env env' (s:Map P env env') : Map P env (S env') := fun var => wk ops (s var).
  Implicit Arguments shiftMap [env env'].

  Lemma shiftConsMap : forall env env' (s:Map P env env') (v:P env'), shiftMap (consMap v s) = consMap (wk ops v) (shiftMap s). 
  Proof.
  intros env env' s v. apply MapExtensional.
  intros v0. 
  dependent destruction v0. simpl. auto. 

  simpl. 
  unfold shiftMap. simpl. auto. 
  Qed.


  Fixpoint travVal env env' (v : Value env) : Map P env env' -> Value env' :=
  match v with
    | NUM _ n => fun m => NUM n
    | VAR _ v => fun m => vl ops (m v)
    | LAMBDA _ e => fun m => LAMBDA (travExp e (lift m))
  end
  with travExp env env' (e : Exp env) : Map P env env' -> Exp env' :=
   match e with
    | OP _ op e1 e2 => fun m => OP op (travVal e1 m) (travVal e2 m)
    | VAL _ v => fun m => VAL (travVal v  m)
    | IFZ _ v e1 e2 => fun m => IFZ (travVal v m) (travExp e1 m) (travExp e2 m)
    | APP _ e1 e2 => fun m => APP (travVal e1 m) (travVal e2 m)
    | LET _ e1 e2 => fun m => LET (travExp e1 m) (travExp e2 (lift m))
  end.

  Definition mapVal env env' m v := @travVal env env' v m.
  Definition mapExp env env' m e := @travExp env env' e m.

  Variable env env' : Env.
  Variable s : Map P env env'.

(*  Lemma mapTVAR : forall (var : Var env t1), mapVal s (TVAR var) = TVAR (s var). auto. Qed. *)
  Lemma mapNUM : forall n, mapVal s (NUM n) = NUM n. auto. Qed.
  Lemma mapLAMBDA : forall (e:Exp (S env)), mapVal s (LAMBDA e) = LAMBDA (mapExp (lift s) e). auto. Qed.
  Lemma mapOP : forall op v1 v2, mapExp s (OP op v1 v2) = OP op (mapVal s v1) (mapVal s v2). auto. Qed.
  Lemma mapVAL : forall (v:Value env), mapExp s (VAL v) = VAL (mapVal s v). auto. Qed.
  Lemma mapLET : forall (e1:Exp env) (e2:Exp (S env)), mapExp s (LET e1 e2) = LET (mapExp s e1) (mapExp (lift s) e2). auto. Qed.
  Lemma mapIFZ : forall v (e1 e2:Exp env), mapExp s (IFZ v e1 e2) = IFZ (mapVal s v) (mapExp s e1) (mapExp s e2). auto. Qed.
  Lemma mapAPP : forall (v1:Value env) v2, mapExp s (APP v1 v2) = APP (mapVal s v1) (mapVal s v2). auto. Qed.

End MapOps.


Hint Rewrite mapNUM mapLAMBDA mapOP mapVAL mapLET mapIFZ mapAPP : mapHints.

Implicit Arguments lift [P env env'].
Implicit Arguments shiftMap [P env env'].


(*==========================================================================
  Variable renamings: Map Var
  ==========================================================================*)

Definition Renaming := Map Var. 
Definition RenamingMapOps := (Build_MapOps (P:=Var) (fun _ v => v) VAR SVAR).
Canonical Structure RenamingMapOps.

(* E E' t are implicit *)
Definition renameVal := mapVal RenamingMapOps.
Definition renameExp := mapExp RenamingMapOps.
Definition liftRenaming := lift RenamingMapOps. 
Implicit Arguments liftRenaming [env env'].
Definition shiftRenaming := shiftMap RenamingMapOps.
Implicit Arguments shiftRenaming [env env'].

Section RenamingDefs.

  Variable E E' : Env.
  Variable s : Renaming E E'.

  Lemma renameVAR : forall (var : Var E), renameVal s (VAR var) = VAR (s var). auto. Qed.
  Lemma renameNUM : forall n, renameVal s (NUM n) = NUM n. auto. Qed.
  Lemma renameLAMBDA : forall (e:Exp (S E)), renameVal s (LAMBDA e) = LAMBDA (renameExp (liftRenaming s) e). auto. Qed.
  Lemma renameOP : forall op v1 v2, renameExp s (OP op v1 v2) = OP op (renameVal s v1) (renameVal s v2). auto. Qed.
  Lemma renameVAL : forall (v:Value E), renameExp s (VAL v) = VAL (renameVal s v). auto. Qed.
  Lemma renameLET : forall (e1:Exp E) (e2:Exp (S E)), renameExp s (LET e1 e2) = LET (renameExp s e1) (renameExp (liftRenaming s) e2). auto. Qed.
  Lemma renameIFZ : forall v (e1 e2:Exp E), renameExp s (IFZ v e1 e2) = IFZ (renameVal s v) (renameExp s e1) (renameExp s e2). auto. Qed.
  Lemma renameAPP : forall (v1:Value E) v2, renameExp s (APP v1 v2) = APP (renameVal s v1) (renameVal s v2). auto. Qed.

End RenamingDefs.

Hint Rewrite renameVAR renameNUM renameLAMBDA renameOP renameVAL renameLET renameIFZ renameAPP : renameHints.

Lemma LiftRenamingDef : forall E E' (r:Renaming E' E), liftRenaming r = consMap (ZVAR _) (shiftRenaming r).
intros. apply MapExtensional. auto.  Qed.

(*==========================================================================
  Identity renaming
  ==========================================================================*)

Definition idRenaming E : Renaming E E := fun (x:Var E) => x.
Implicit Arguments idRenaming [].

Lemma liftIdRenaming : forall E, liftRenaming (idRenaming E) = idRenaming (S E).
intros E. apply MapExtensional.  
dependent destruction var; auto. 
Qed.

Lemma applyIdRenaming : 
   (forall E (v:Value E), renameVal (idRenaming E) v = v)
/\ (forall E (e:Exp E), renameExp (idRenaming E) e = e).
Proof.
apply ExpValue_ind; 
(intros; try (autorewrite with renameHints using try rewrite liftIdRenaming; try rewrite liftIdRenaming; try rewrite H; try rewrite H0; try rewrite H1); auto).
Qed.

Lemma idRenamingDef : forall E, idRenaming (S E) = consMap (ZVAR _) (shiftRenaming (idRenaming E)).
intros. apply MapExtensional. intros. dependent destruction var; auto. Qed.


(*==========================================================================
  Composition of renaming
  ==========================================================================*)

Definition composeRenaming P E E' E'' (m:Map P E' E'') (r : Renaming E E') : Map P E E'' := fun var => m (r var). 

Lemma liftComposeRenaming : forall E E' E'' (s':Renaming E' E'') (s:Renaming E E'), liftRenaming (composeRenaming s' s) = composeRenaming (liftRenaming s') (liftRenaming s).
intros. apply MapExtensional. intros var.
dependent destruction var; auto. 
Qed.

Lemma liftMapComposeRenaming : forall P ops E E' E'' (m:Map P E' E'') (r:Renaming E E'), lift ops (composeRenaming m r) = composeRenaming (lift ops m) (liftRenaming r).
intros. apply MapExtensional. intros var.
dependent destruction var; auto. 
Qed.

Lemma applyComposeRenaming : 
   (forall E (v:Value E) P ops E' E'' (m:Map P E' E'') (s : Renaming E E'),
    mapVal ops (composeRenaming m s) v = mapVal ops m (renameVal s v))
/\ (forall E (e:Exp   E) P ops E' E'' (m:Map P E' E'') (s : Renaming E E'),
    mapExp ops (composeRenaming m s) e = mapExp ops m (renameExp s e)).
Proof.
apply ExpValue_ind; intros; 
autorewrite with mapHints renameHints; try rewrite liftMapComposeRenaming; try rewrite liftMapComposeRenaming; try rewrite <- H;
try rewrite <- H0; try rewrite <- H1; auto.  
Qed.

Lemma composeRenamingAssoc : forall P E E' E'' E''' (m:Map P E'' E''') r' (r:Renaming E E'), composeRenaming m (composeRenaming r' r) = composeRenaming (composeRenaming m r') r.
Proof. auto. Qed.

Lemma composeRenamingIdLeft : forall E E' (r:Renaming E E'), composeRenaming (idRenaming _) r = r.
Proof. intros. apply MapExtensional. auto. Qed.

Lemma composeRenamingIdRight : forall P E E' (m:Map P E E'), composeRenaming m (idRenaming _) = m.
Proof. intros. apply MapExtensional. auto. Qed.

(*==========================================================================
  Substitution
  ==========================================================================*)

Definition Subst := Map Value.
Definition SubstMapOps := Build_MapOps (P:=Value) VAR (fun _ v => v) (fun E => renameVal (fun v => SVAR v)). 

(* Convert a renaming into a substitution *)
Definition renamingToSubst E E' (r:Renaming E E') : Subst E E' := fun v => VAR (r v).

Definition substVal := mapVal SubstMapOps.
Definition substExp := mapExp SubstMapOps.

Definition shiftSubst := shiftMap SubstMapOps.
Implicit Arguments shiftSubst [env env'].

Definition liftSubst := lift SubstMapOps.
Implicit Arguments liftSubst [env env']. 

Section SubstDefs.

  Variable E E' : Env.
  Variable s : Subst E E'.

  Lemma substVAR : forall (var : Var E), substVal s (VAR var) = s var. auto. Qed.
  Lemma substNUM : forall n, substVal s (NUM n) = NUM n. auto. Qed.
  Lemma substLAMBDA : forall (e:Exp (S E)), substVal s (LAMBDA e) = LAMBDA (substExp (liftSubst s) e). auto. Qed.
  Lemma substOP : forall op v1 v2, substExp s (OP op v1 v2) = OP op (substVal s v1) (substVal s v2). auto. Qed.
  Lemma substVAL : forall (v:Value E), substExp s (VAL v) = VAL (substVal s v). auto. Qed.
  Lemma substLET : forall (e1:Exp E) (e2:Exp (S E)), substExp s (LET e1 e2) = LET (substExp s e1) (substExp (liftSubst s) e2). auto. Qed.
  Lemma substIFZ : forall v (e1 e2:Exp E), substExp s (IFZ v e1 e2) = IFZ (substVal s v) (substExp s e1) (substExp s e2). auto. Qed.
  Lemma substAPP : forall (v1:Value E) v2, substExp s (APP v1 v2) = APP (substVal s v1) (substVal s v2). auto. Qed.

End SubstDefs.

Hint Rewrite substVAR substNUM substLAMBDA substOP substVAL substLET substIFZ substAPP : substHints.


(*==========================================================================
  Identity substitution
  ==========================================================================*)

Definition idSubst E : Subst E E := fun (x:Var E) => VAR x.
Implicit Arguments idSubst [].

Lemma liftIdSubst : forall E, liftSubst (idSubst E) = idSubst (S E).
intros E. apply MapExtensional. unfold liftSubst. intros.
dependent destruction var; auto. 
Qed.

Lemma applyIdSubst : 
   (forall E (v:Value E), substVal (idSubst E) v = v)
/\ (forall E (e:Exp E), substExp (idSubst E) e = e).
Proof.
apply ExpValue_ind; intros; autorewrite with substHints; try rewrite liftIdSubst; try rewrite liftIdSubst; try rewrite H; try rewrite H0; try rewrite H1; auto.
Qed.

Notation "[ x , .. , y ]" := (consMap x .. (consMap y (idSubst _)) ..) : Subst_scope. 
Delimit Scope Subst_scope with subst.
Arguments Scope substExp [_ Subst_scope]. 
Arguments Scope substVal [_ Subst_scope]. 


Lemma LiftSubstDef : forall E E' (s:Subst E' E), liftSubst s = consMap (VAR (ZVAR _)) (shiftSubst s).
intros. apply MapExtensional. intros. dependent destruction var; auto. Qed.

Lemma hdLiftConsSubst : forall E E' (v:Value E') (s:Subst E E'), hdMap (liftSubst (consMap v s)) = VAR (ZVAR _). 
Proof. intros. rewrite LiftSubstDef. rewrite hdConsMap. trivial. Qed.

Lemma liftConsSubst : forall E E' (v:Value E') (s:Subst E E'), liftSubst (consMap v s) = consMap (VAR (ZVAR  _)) (consMap (renameVal (fun v => SVAR v) v) (shiftSubst s)). 
intros. rewrite LiftSubstDef. unfold shiftSubst. rewrite shiftConsMap. auto. 
Qed.


(*==========================================================================
  Composition of substitution followed by renaming
  ==========================================================================*)

Definition composeRenamingSubst E E' E'' (r:Renaming E' E'') (s : Subst E E') : Subst E E'' := fun var => renameVal r (s var). 

Lemma liftComposeRenamingSubst : forall E E' E'' (r:Renaming E' E'') (s:Subst E E'), liftSubst (composeRenamingSubst r s) = composeRenamingSubst (liftRenaming r) (liftSubst s).
intros. apply MapExtensional. intros var. dependent induction var; auto. 
simpl. unfold composeRenamingSubst. unfold liftSubst. simpl. unfold renameVal at 1. rewrite <- (proj1 applyComposeRenaming). unfold renameVal. rewrite <- (proj1 applyComposeRenaming). 
auto. 
Qed.

Lemma applyComposeRenamingSubst :
   (forall E (v:Value E) E' E'' (r:Renaming E' E'') (s : Subst E E'),
    substVal (composeRenamingSubst r s) v = renameVal r (substVal s v))
/\ (forall E (e:Exp   E) E' E'' (r:Renaming E' E'') (s : Subst E E'),
    substExp (composeRenamingSubst r s) e = renameExp r (substExp s e)).
Proof.
apply ExpValue_ind;
(intros; try (autorewrite with substHints renameHints using try rewrite liftComposeRenamingSubst; try rewrite liftComposeRenamingSubst; try rewrite H; try rewrite H0; try rewrite H1); auto).
Qed.

(*==========================================================================
  Composition of substitutions
  ==========================================================================*)

Definition composeSubst E E' E'' (s':Subst E' E'') (s : Subst E E') : Subst E E'' := fun var => substVal s' (s var). 

Arguments Scope composeSubst [_ _ _ Subst_scope Subst_scope]. 

Lemma liftComposeSubst : forall E E' E'' (s':Subst E' E'') (s:Subst E E'), liftSubst (composeSubst s' s) = composeSubst (liftSubst s') (liftSubst s).
intros. apply MapExtensional. intros var. dependent destruction var. auto.
unfold composeSubst. simpl. 
rewrite <- (proj1 applyComposeRenamingSubst). unfold composeRenamingSubst. unfold substVal. 
rewrite <- (proj1 applyComposeRenaming). auto.
Qed.

Lemma substComposeSubst : 
   (forall E (v:Value E) E' E'' (s':Subst E' E'') (s : Subst E E'),
    substVal (composeSubst s' s) v = substVal s' (substVal s v))
/\ (forall E (e:Exp   E) E' E'' (s':Subst E' E'') (s : Subst E E'),
    substExp (composeSubst s' s) e = substExp s' (substExp s e)).
Proof.
apply ExpValue_ind;
(intros; try (autorewrite with substHints using try rewrite liftComposeSubst; try rewrite liftComposeSubst; try rewrite H; try rewrite H0; try rewrite H1); auto).
Qed.

Lemma composeCons : forall E E' E'' (s':Subst E' E'') (s:Subst E E') (v:Value _), 
  composeSubst (consMap v s') (liftSubst s) = consMap v (composeSubst s' s).
intros. apply MapExtensional. intros var.  dependent destruction var. auto. 
unfold composeSubst. simpl. unfold substVal. rewrite <- (proj1 applyComposeRenaming). unfold composeRenaming. simpl.
assert ((fun (var0:Var E') => s' var0) = s') by (apply MapExtensional; auto). 
rewrite H. auto. 
Qed.

Lemma composeSubstIdLeft : forall E E' (s:Subst E E'), composeSubst (idSubst _) s = s.
Proof. intros. apply MapExtensional. intros. unfold composeSubst. apply (proj1 applyIdSubst). Qed.

Lemma composeSubstIdRight : forall E E' (s:Subst E E'), composeSubst s (idSubst _) = s.
Proof. intros. apply MapExtensional. auto.  
Qed.


(*==========================================================================
  Constructors are injective 
  ==========================================================================*)

Lemma TVAL_injective : 
  forall env (v1 : Value env) v2, 
  VAL v1 = VAL v2 -> 
  v1 = v2.
intros.
dependent destruction H. trivial.
Qed.

Lemma LAMBDA_injective : 
  forall env (e1:Exp (S env)) e2,
  LAMBDA e1 = LAMBDA e2 -> 
  e1 = e2.
intros.
dependent destruction H. trivial.
Qed.

(*==========================================================================
  Closed forms
  ==========================================================================*)
Lemma ClosedValue : forall (v:CValue), (exists b, v = LAMBDA b) \/ (exists i, v = NUM i).
unfold CValue.
intros v.
dependent destruction v.
(* TVAR case: impossible *)
dependent destruction v.
(* TNUM case *)
right. exists n. trivial.
(* TLAMBDA case *)
left. exists e. trivial.
Qed.

Unset Implicit Arguments.
