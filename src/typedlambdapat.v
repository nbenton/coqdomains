(*==========================================================================
  Call-by-value simply-typed lambda-calculus with recursion, pairs, and arithmetic
  ==========================================================================*)

Require Import utility.
Require Import List.
Require Import Program.Equality.
Set Implicit Arguments.
Unset Strict Implicit.
Set Printing Implicit Defensive.

(*====== coqdoc printing directives ========================================*)
(** printing --> %\ensuremath{\mathrel{\texttt{->}}}% *)
(** printing ** %\ensuremath{\mathrel{\texttt{*}}}% *)
(** printing Int %{\textsf{Int}}% *)
(** printing Bool %{\textsf{Bool}}% *)
(** printing Arrow %{\textsf{Arrow}}% *)
(** printing Prod %{\textsf{Prod}}% *)
(** printing Ty %{\textsf{Ty}}% *)
(** printing Env %{\textsf{Env}}% *)

(** printing env %{\ensuremath{\Gamma}}% *)
(** printing env' %{\ensuremath{\Gamma'}}% *)
(** printing env1 %{\ensuremath{\Gamma_1}}% *)
(** printing env2 %{\ensuremath{\Gamma_2}}% *)
(** printing env'' %{\ensuremath{\Gamma''}}% *)
(** printing ty %{\ensuremath{\tau}}% *)
(** printing ty1 %\ensuremath{\tau_1}% *)
(** printing ty2 %\ensuremath{\tau_2}% *)
(** printing ty' %\ensuremath{\tau'}% *)
(** printing ++ %\ensuremath{+\!+}% *)

(*==========================================================================
  Types and contexts
  ==========================================================================*)

Inductive Ty := Int | Bool | Arrow (ty1 ty2 : Ty) | Prod (ty1 ty2 : Ty) | Sum (ty1 ty2 : Ty).

Infix " --> " := Arrow. (* (at level 55). *)
Infix " ** " := Prod (at level 55).

Definition Env := list Ty.

(* begin hide *)
Notation "[ x , .. , y ]" := (cons x .. (cons y nil) ..) : list_scope. 
(* end hide *)

(*==========================================================================
  Typed terms in context
  ==========================================================================*)

Inductive Var : Env -> Ty -> Type := 
| ZVAR : forall env ty, Var (ty :: env) ty
| SVAR : forall env ty ty', Var env ty -> Var (ty' :: env) ty.

(*==========================================================================
  Variable-domain maps. 
  By instantiating P with Var we get renamings.
  By instantiating P with Val we get substitutions.
  ==========================================================================*)

Definition Map (P:Env -> Ty -> Type) E E' := forall t, Var E t -> P E' t.

(* Head, tail and cons *)
Definition tlMap P E E' t (m:Map P (t::E) E') : Map P E E' := fun t' v => m t' (SVAR t v).
Definition hdMap P E E' t (m:Map P (t::E) E') : P E' t := m t (ZVAR _ _).
Implicit Arguments tlMap [P E E' t].
Implicit Arguments hdMap [P E E' t].

Program Definition consMap P E E' t (v:P E' t) (m:Map P E E') : Map P (t::E) E' :=
    fun t' (var:Var (t::E) t') => 
    match var with
    | ZVAR _ _ => v
    | SVAR _ _ _ var => m _ var
    end.
Implicit Arguments consMap [P E E' t].

Axiom MapExtensional : forall P E E' (r1 r2 : Map P E E'), (forall t var, r1 t var = r2 t var) -> r1 = r2.

Lemma hdConsMap : forall P env env' ty (v : P env' ty) (s : Map P env env'), hdMap (consMap v s) = v. Proof. auto. Qed.
Lemma tlConsMap : forall P env env' ty (v : P env' ty) (s : Map P env env'), tlMap (consMap v s) = s. Proof. intros. apply MapExtensional. auto. Qed.

Lemma consMapInv : forall P env env' ty (m:Map P (ty :: env) env'), exists m', exists v, m = consMap v m'.  
intros. exists (tlMap m). exists (hdMap m).
apply MapExtensional. dependent destruction var; auto. 
Qed.

Definition Renaming := Map Var. 
Definition composeRenaming P env env' env'' (m : Map P env' env'') (r : Renaming env env') : Map P env env'' := fun t var => m _ (r _ var). 

(* Patterns with no repeated variables *)
Inductive Pat : Env -> Ty -> Type :=
| PPAIR : forall env1 env2 ty1 ty2, Pat env1 ty1 -> Pat env2 ty2 -> Pat (env1++env2) (ty1 ** ty2)
| PVAR : forall ty, Pat [ty] ty
| PWILD : forall ty, Pat nil ty
| PFAIL : forall ty, Pat nil ty
| PAS : forall env ty, Pat env ty -> Pat (ty::env) ty
| PINL : forall env ty1 ty2, Pat env ty1 -> Pat env (Sum ty1 ty2)
| PINR : forall env ty1 ty2, Pat env ty2 -> Pat env (Sum ty1 ty2).

Inductive Value : Env -> Ty -> Type :=
| INT : forall env, nat -> Value env Int
| BOOL : forall env, bool -> Value env Bool
| VAR :> forall env ty, Var env ty -> Value env ty
| FIX : forall env ty1 ty2, Exp (ty1 :: ty1 --> ty2 :: env) ty2 -> Value env (ty1 --> ty2)  
| PAIR : forall env ty1 ty2, Value env ty1 -> Value env ty2 -> Value env (ty1 ** ty2)
| INL : forall env ty1 ty2, Value env ty1 -> Value env (Sum ty1 ty2)
| INR : forall env ty1 ty2, Value env ty2 -> Value env (Sum ty1 ty2)
with Exp : Env -> Ty -> Type :=
| FST : forall env ty1 ty2, Value env (ty1 ** ty2) -> Exp env ty1
| SND : forall env ty1 ty2, Value env (ty1 ** ty2) -> Exp env ty2
| OP : forall env, (nat -> nat -> nat) -> Value env Int -> Value env Int -> Exp env Int
| GT : forall env, Value env Int -> Value env Int -> Exp env Bool
| VAL : forall env ty, Value env ty -> Exp env ty
| LET : forall env ty1 ty2, Exp env ty1 -> Exp (ty1 :: env) ty2 -> Exp env ty2 
| LETPAT : forall env env' ty1 ty2, Exp env ty1 -> Pat env' ty1 -> Exp (env'++env) ty2 -> Exp env ty2
| APP : forall env ty1 ty2, Value env (ty1 --> ty2) -> Value env ty1 -> Exp env ty2
| COND : forall env ty, Value env Bool -> Exp env ty -> Exp env ty -> Exp env ty.

Implicit Arguments BOOL [env].
Implicit Arguments INT [env].

(* begin hide *)
Scheme Val_rec2 := Induction for Value Sort Set
  with Exp_rec2 := Induction for Exp Sort Set.

Scheme Val_type2 := Induction for Value Sort Type
  with Exp_type2 := Induction for Exp Sort Type.

Scheme Val_ind2 := Induction for Value Sort Prop
  with Exp_ind2 := Induction for Exp Sort Prop.

Combined Scheme ExpVal_ind from Val_ind2, Exp_ind2.
(* end hide *)

(* Closed expressions and values *)
Definition CExp ty := Exp nil ty.
Definition CValue ty := Value nil ty.

(*==========================================================================
  Package of operations used with a Map
    vr maps a Var into Var or Value (so is either the identity or VAR)
    vl maps a Var or Value to a Value (so is either VAR or the identity)
    wk weakens a Var or Value (so is either SVAR or renaming through SVAR on a value)
  ==========================================================================*)
Record MapOps (P : Env -> Ty -> Type) :=
{
  vr : forall env ty, Var env ty -> P env ty;   
  vl : forall env ty, P env ty -> Value env ty;
  wk : forall env ty ty', P env ty -> P (ty' :: env) ty
}.

Section MapOps.

  Variable P : Env -> Ty -> Type.
  Variable ops : MapOps P.

  Program Definition lift env env' ty (m : Map P env env') : Map P (ty::env) (ty::env') :=
  fun ty' => fun var => match var with
  | ZVAR _ _ => vr ops (ZVAR _ _)
  | SVAR _ _ _ x => wk ops _ (m _ x)
  end.
  Implicit Arguments lift [env env'].

  Fixpoint liftAux env env' env'' (m : Map P env env') : Map P (env'' ++ env) (env'' ++ env') :=
  match env'' with
  | nil => m
  | (ty :: env'') => lift ty (liftAux (env'':=env'') m) 
  end.
  Implicit Arguments liftAux [env env'].

  Definition shiftMap env env' ty (m : Map P env env') : Map P env (ty :: env') := fun ty' => fun var => wk ops _ (m ty' var).
  Implicit Arguments shiftMap [env env'].

  Lemma shiftConsMap : forall env env' ty (m : Map P env env') (x : P env' ty) ty', shiftMap ty' (consMap x m) = consMap (wk ops _ x) (shiftMap ty' m). 
  Proof.
  intros env env' ty m x ty'. apply MapExtensional.
  intros ty0 var0. dependent destruction var0; auto.
  Qed.

  Fixpoint travVal env env' ty (v : Value env ty) : Map P env env' -> Value env' ty :=
  match v with
    | INT _ i => fun m => INT i
    | BOOL _ b => fun m => BOOL b
    | VAR _ _ v => fun m => vl ops (m _ v)
    | FIX _ _ _ e => fun m => FIX (travExp e (lift _ (lift _ m)))
    | PAIR _ _ _ e1 e2 => fun m => PAIR (travVal e1 m) (travVal e2 m)
    | INL _ _ _ e => fun m => INL _ (travVal e m)
    | INR _ _ _ e => fun m => INR _ (travVal e m)
  end
  with travExp env env' ty (e : Exp env ty) : Map P env env' -> Exp env' ty :=
   match e with
    | OP _ op e1 e2 => fun m => OP op (travVal e1 m) (travVal e2 m)
    | GT _ e1 e2 => fun m => GT (travVal e1 m) (travVal e2 m)
    | FST _ _ _ e => fun m => FST (travVal e m)
    | SND _ _ _ e => fun m => SND (travVal e m)
    | VAL _ _ v => fun m => VAL (travVal v  m)
    | COND _ _ v e1 e2 => fun m => COND (travVal v m) (travExp e1 m) (travExp e2 m)
    | APP _ _ _ e1 e2 => fun m => APP (travVal e1 m) (travVal e2 m)
    | LET _ _ _ e1 e2 => fun m => LET (travExp e1 m) (travExp e2 (lift _ m))
    | LETPAT _ _ _ _ e1 p e2 => fun m => LETPAT (travExp e1 m) p (travExp e2 (liftAux _ m) )
  end.

  Definition mapVal env env' ty m v := @travVal env env' ty v m.
  Definition mapExp env env' ty m e := @travExp env env' ty e m.

  Variable env env' : Env.
  Variable m : Map P env env'.
  Variable ty1 ty2 : Ty.

  Lemma mapVAR : forall (var : Var _ ty1), mapVal m (VAR var) = vl ops (m var). auto. Qed. 
  Lemma mapINT : forall n, mapVal m (INT n) = INT n. auto. Qed.
  Lemma mapBOOL : forall n, mapVal m (BOOL n) = BOOL n. auto. Qed.
  Lemma mapINL : forall (v1 : Value _ ty1), mapVal m (INL ty2 v1) = INL _ (mapVal m v1). auto. Qed.
  Lemma mapINR : forall (v2 : Value _ ty2), mapVal m (INR ty1 v2) = INR _ (mapVal m v2). auto. Qed.
  Lemma mapPAIR : forall (v1 : Value _ ty1) (v2 : Value _ ty2), mapVal m (PAIR v1 v2) = PAIR (mapVal m v1) (mapVal m v2). auto. Qed. 
  Lemma mapFST : forall (v : Value _ (ty1 ** ty2)), mapExp m (FST v) = FST (mapVal m v). auto. Qed.
  Lemma mapSND : forall (v : Value _ (ty1 ** ty2)), mapExp m (SND v) = SND (mapVal m v). auto. Qed.
  Lemma mapFIX : forall (e : Exp (ty1 :: ty1-->ty2 :: _) ty2), mapVal m (FIX e) = FIX (mapExp (lift _ (lift _ m)) e). auto. Qed.
  Lemma mapOP : forall op v1 v2, mapExp m (OP op v1 v2) = OP op (mapVal m v1) (mapVal m v2). auto. Qed.
  Lemma mapGT : forall v1 v2, mapExp m (GT v1 v2) = GT (mapVal m v1) (mapVal m v2). auto. Qed.
  Lemma mapVAL : forall (v : Value _ ty1), mapExp m (VAL v) = VAL (mapVal m v). auto. Qed.
  Lemma mapLET : forall (e1 : Exp _ ty1) (e2 : Exp _ ty2), mapExp m (LET e1 e2) = LET (mapExp m e1) (mapExp (lift _ m) e2). auto. Qed.
  Lemma mapLETPAT : forall env'', forall (e1 : Exp _ ty1) (p : Pat env'' _) (e2 : Exp _ ty2), mapExp m (LETPAT e1 p e2) = LETPAT (mapExp m e1) p (mapExp (liftAux _ m) e2). auto. Qed.
  Lemma mapCOND : forall v (e1 e2 : Exp _ ty1), mapExp m (COND v e1 e2) = COND (mapVal m v) (mapExp m e1) (mapExp m e2). auto. Qed.
  Lemma mapAPP : forall (v1 : Value _ (ty1 --> ty2)) v2, mapExp m (APP v1 v2) = APP (mapVal m v1) (mapVal m v2). auto. Qed.

End MapOps.

Hint Rewrite mapVAR mapINT mapBOOL mapPAIR mapFST mapSND mapFIX mapOP mapGT mapVAL mapLET mapLETPAT mapCOND mapAPP mapINL mapINR : mapHints.

Implicit Arguments lift [P env env'].
Implicit Arguments liftAux [P env env'].
Implicit Arguments shiftMap [P env env'].

(*==========================================================================
  Variable renamings: Map Var
  ==========================================================================*)

Definition RenamingMapOps := (Build_MapOps (fun _ _ v => v) VAR SVAR).

Definition renameVal := mapVal RenamingMapOps.
Definition renameExp := mapExp RenamingMapOps.
Definition liftRenaming := lift RenamingMapOps. 
Definition liftAuxRenaming := liftAux RenamingMapOps.
Implicit Arguments liftRenaming [env env'].
Implicit Arguments liftAuxRenaming [env env'].
Definition shiftRenaming := shiftMap RenamingMapOps.
Implicit Arguments shiftRenaming [env env'].

Section RenamingDefs.

  Variable env env' : Env.
  Variable r : Renaming env env'.
  Variable ty1 ty2 : Ty.

  Lemma renameVAR : forall (var : Var env ty1), renameVal r (VAR var) = VAR (r var). auto. Qed.
  Lemma renameINT : forall n, renameVal r (INT n) = INT n. auto. Qed.
  Lemma renameBOOL : forall n, renameVal r (BOOL n) = BOOL n. auto. Qed.
  Lemma renameINL : forall (v1 : Value _ ty1), renameVal r (INL ty2 v1) = INL _ (renameVal r v1). auto. Qed.
  Lemma renameINR : forall (v2 : Value _ ty2), renameVal r (INR ty1 v2) = INR _ (renameVal r v2). auto. Qed.
  Lemma renamePAIR : forall (v1 : Value _ ty1) (v2 : Value _ ty2), renameVal r (PAIR v1 v2) = PAIR (renameVal r v1) (renameVal r v2). auto. Qed.
  Lemma renameFST : forall (v : Value _ (ty1 ** ty2)), renameExp r (FST v) = FST (renameVal r v). auto. Qed.
  Lemma renameSND : forall (v : Value _ (ty1 ** ty2)), renameExp r (SND v) = SND (renameVal r v). auto. Qed.
  Lemma renameFIX : forall (e : Exp (ty1 :: ty1-->ty2 :: _) ty2), renameVal r (FIX e) = FIX (renameExp (liftRenaming _ (liftRenaming _ r)) e). auto. Qed.
  Lemma renameOP : forall op v1 v2, renameExp r (OP op v1 v2) = OP op (renameVal r v1) (renameVal r v2). auto. Qed.
  Lemma renameGT : forall v1 v2, renameExp r (GT v1 v2) = GT (renameVal r v1) (renameVal r v2). auto. Qed.
  Lemma renameVAL : forall (v : Value env ty1), renameExp r (VAL v) = VAL (renameVal r v). auto. Qed.
  Lemma renameLET : forall (e1 : Exp _ ty1) (e2 : Exp _ ty2), renameExp r (LET e1 e2) = LET (renameExp r e1) (renameExp (liftRenaming _ r) e2). auto. Qed.
  Lemma renameLETPAT : forall env'' (e1 : Exp _ ty1) (p : Pat env'' _) (e2 : Exp _ ty2), renameExp r (LETPAT e1 p e2) = LETPAT (renameExp r e1) p (renameExp (liftAuxRenaming _ r) e2). auto. Qed.
  Lemma renameCOND : forall v (e1 e2 : Exp _ ty1), renameExp r (COND v e1 e2) = COND (renameVal r v) (renameExp r e1) (renameExp r e2). auto. Qed.
  Lemma renameAPP : forall (v1 : Value _ (ty1-->ty2)) v2, renameExp r (APP v1 v2) = APP (renameVal r v1) (renameVal r v2). auto. Qed.

End RenamingDefs.

Hint Rewrite renameVAR renameINT renameBOOL renamePAIR renameFST renameSND renameFIX renameOP renameGT renameVAL renameLET renameLETPAT renameCOND renameAPP renameINL renameINR
 : renameHints.

Lemma LiftRenamingDef : forall env env' (r : Renaming env' env) ty, liftRenaming _ r = consMap (ZVAR _ ty) (shiftRenaming _ r).
intros. apply MapExtensional. auto.  Qed.

(*==========================================================================
  Identity renaming
  ==========================================================================*)

Definition idRenaming env : Renaming env env := fun ty (var : Var env ty) => var.
Implicit Arguments idRenaming [].

Lemma liftIdRenaming : forall E t, liftRenaming _ (idRenaming E) = idRenaming (t::E).
intros. apply MapExtensional.  
dependent destruction var; auto. 
Qed.

Lemma liftAuxIdRenaming : forall env' env, liftAuxRenaming _ (idRenaming env) = idRenaming (env' ++ env).
induction env'. auto. 
intros. simpl. rewrite IHenv'. apply MapExtensional. dependent destruction var; auto. 
Qed.

Lemma applyIdRenaming : 
   (forall env ty (v : Value env ty), renameVal (idRenaming env) v = v)
/\ (forall env ty (e : Exp env ty), renameExp (idRenaming env) e = e).
Proof.
apply ExpVal_ind; 
(intros; try (autorewrite with renameHints using try rewrite liftIdRenaming; try rewrite liftIdRenaming; try rewrite liftAuxIdRenaming; try rewrite H; try rewrite H0; try rewrite H1); auto).
Qed.

Lemma idRenamingDef : forall ty env, idRenaming (ty :: env) = consMap (ZVAR _ _) (shiftRenaming ty (idRenaming env)).
intros. apply MapExtensional. intros. dependent destruction var; auto. Qed.


(*==========================================================================
  Composition of renaming
  ==========================================================================*)

Lemma liftComposeRenaming : forall P ops E env' env'' t (m:Map P env' env'') (r:Renaming E env'), lift ops t (composeRenaming m r) = composeRenaming (lift ops t m) (liftRenaming t r).
intros. apply MapExtensional. intros t0 var.
dependent destruction var; auto. 
Qed.

Lemma liftAuxComposeRenaming : forall env''' P ops E env' env'' (m:Map P env' env'') (r:Renaming E env'), liftAux ops env''' (composeRenaming m r) = composeRenaming (liftAux ops env''' m) (liftAuxRenaming env''' r).
induction env'''.  auto. 
intros. simpl. rewrite IHenv'''. apply MapExtensional. intros t0 var.
dependent destruction var; auto. 
Qed.

Lemma applyComposeRenaming : 
   (forall env ty (v : Value env ty) P ops env' env'' (m:Map P env' env'') (s : Renaming env env'),
    mapVal ops (composeRenaming m s) v = mapVal ops m (renameVal s v))
/\ (forall env ty (e : Exp   env ty) P ops env' env'' (m:Map P env' env'') (s : Renaming env env'),
    mapExp ops (composeRenaming m s) e = mapExp ops m (renameExp s e)).
Proof.
apply ExpVal_ind; intros; 
autorewrite with mapHints renameHints; try rewrite liftComposeRenaming; try rewrite liftComposeRenaming; try rewrite liftAuxComposeRenaming; try rewrite <- H;
try rewrite <- H0; try rewrite <- H1; auto.  
Qed.

Lemma composeRenamingAssoc : 
  forall P env env' env'' env''' (m : Map P env'' env''') r' (r : Renaming env env'), 
  composeRenaming m (composeRenaming r' r) = composeRenaming (composeRenaming m r') r.
Proof. auto. Qed.

Lemma composeRenamingIdLeft : forall env env' (r : Renaming env env'), composeRenaming (idRenaming _) r = r.
Proof. intros. apply MapExtensional. auto. Qed.

Lemma composeRenamingIdRight : forall P env env' (m:Map P env env'), composeRenaming m (idRenaming _) = m.
Proof. intros. apply MapExtensional. auto. Qed.

(*==========================================================================
  Substitution
  ==========================================================================*)

Definition Subst := Map Value.
Definition SubstMapOps := Build_MapOps VAR (fun _ _ v => v) (fun env ty ty' => renameVal (fun _ => SVAR ty')). 

(* Convert a renaming into a substitution *)
Definition renamingToSubst env env' (r : Renaming env env') : Subst env env' := fun ty => fun v => VAR (r ty v).

Definition substVal := mapVal SubstMapOps.
Definition substExp := mapExp SubstMapOps.

Definition shiftSubst := shiftMap SubstMapOps.
Implicit Arguments shiftSubst [env env'].

Definition liftSubst := lift SubstMapOps.
Implicit Arguments liftSubst [env env']. 

Definition liftAuxSubst := liftAux SubstMapOps.
Implicit Arguments liftAuxSubst [env env']. 

Section SubstDefs.

  Variable env env' : Env.
  Variable s : Subst env env'.
  Variable ty1 ty2 : Ty.

  Lemma substVAR : forall (var : Var env ty1), substVal s (VAR var) = s var. auto. Qed.
  Lemma substINT : forall n, substVal s (INT n) = INT n. auto. Qed.
  Lemma substBOOL : forall n, substVal s (BOOL n) = BOOL n. auto. Qed.
  Lemma substINL : forall (v1 : Value _ ty1), substVal s (INL ty2 v1) = INL _ (substVal s v1). auto. Qed.
  Lemma substINR : forall (v2 : Value _ ty2), substVal s (INR ty1 v2) = INR _ (substVal s v2). auto. Qed.
  Lemma substPAIR : forall (v1 : Value _ ty1) (v2:Value _ ty2), substVal s (PAIR v1 v2) = PAIR (substVal s v1) (substVal s v2). auto. Qed.
  Lemma substFST : forall (v : Value _ (ty1 ** ty2)), substExp s (FST v) = FST (substVal s v). auto. Qed.
  Lemma substSND : forall (v : Value _ (ty1 ** ty2)), substExp s (SND v) = SND (substVal s v). auto. Qed.
  Lemma substFIX : forall (e : Exp (ty1 :: ty1-->ty2 :: _) ty2), substVal s (FIX e) = FIX (substExp (liftSubst _ (liftSubst _ s)) e). auto. Qed.
  Lemma substOP : forall op v1 v2, substExp s (OP op v1 v2) = OP op (substVal s v1) (substVal s v2). auto. Qed.
  Lemma substGT : forall v1 v2, substExp s (GT v1 v2) = GT (substVal s v1) (substVal s v2). auto. Qed.
  Lemma substVAL : forall (v : Value _ ty1), substExp s (VAL v) = VAL (substVal s v). auto. Qed.
  Lemma substLET : forall (e1 : Exp _ ty1) (e2 : Exp _ ty2), substExp s (LET e1 e2) = LET (substExp s e1) (substExp (liftSubst _ s) e2). auto. Qed.
  Lemma substLETPAT : forall env'' (e1 : Exp _ ty1) (p:Pat env'' _) (e2 : Exp _ ty2), substExp s (LETPAT e1 p e2) = LETPAT (substExp s e1) p (substExp (liftAuxSubst _ s) e2). auto. Qed.
  Lemma substCOND : forall v (e1 e2 : Exp _ ty1), substExp s (COND v e1 e2) = COND (substVal s v) (substExp s e1) (substExp s e2). auto. Qed.
  Lemma substAPP : forall (v1:Value _ (ty1 --> ty2)) v2, substExp s (APP v1 v2) = APP (substVal s v1) (substVal s v2). auto. Qed.

End SubstDefs.

Hint Rewrite substVAR substPAIR substINT substBOOL substFST substSND substFIX substOP substGT substVAL substLET substLETPAT substCOND substAPP substINR substINL : substHints.


(*==========================================================================
  Identity substitution
  ==========================================================================*)

Definition idSubst env : Subst env env := fun ty (x:Var env ty) => VAR x.
Implicit Arguments idSubst [].

Lemma liftIdSubst : forall env ty, liftSubst ty (idSubst env) = idSubst (ty :: env).
intros env ty. apply MapExtensional. unfold liftSubst. intros.
dependent destruction var; auto. 
Qed.

Lemma liftAuxIdSubst : forall env' env, liftAuxSubst env' (idSubst env) = idSubst (env' ++ env).
induction env'. auto. 
intros. simpl. rewrite IHenv'. apply MapExtensional. intros.
dependent destruction var; auto. 
Qed.

Lemma applyIdSubst : 
   (forall env ty (v : Value env ty), substVal (idSubst env) v = v)
/\ (forall env ty (e : Exp env ty), substExp (idSubst env) e = e).
Proof.
apply ExpVal_ind; intros; autorewrite with substHints; try rewrite liftIdSubst; try rewrite liftIdSubst; try rewrite liftAuxIdSubst; try rewrite H; try rewrite H0; try rewrite H1; auto.
Qed.

Notation "[ x , .. , y ]" := (consMap x .. (consMap y (idSubst _)) ..) : Subst_scope. 
Delimit Scope Subst_scope with subst.
Arguments Scope substExp [_ _ Subst_scope]. 
Arguments Scope substVal [_ _ Subst_scope]. 

Lemma LiftSubstDef : forall env env' ty (s : Subst env' env), liftSubst ty s = consMap (VAR (ZVAR _ _)) (shiftSubst ty s).
intros. apply MapExtensional. intros. dependent destruction var; auto. Qed.

(*==========================================================================
  Composition of substitution followed by renaming
  ==========================================================================*)

Definition composeRenamingSubst env env' env'' (r : Renaming env' env'') (s : Subst env env') : Subst env env'' := fun t var => renameVal r (s _ var). 

Lemma liftComposeRenamingSubst : forall E env' env'' t (r:Renaming env' env'') (s:Subst E env'), liftSubst t (composeRenamingSubst r s) = composeRenamingSubst (liftRenaming t r) (liftSubst t s).
intros. apply MapExtensional. intros t0 var. dependent induction var; auto. 
simpl. unfold composeRenamingSubst. unfold liftSubst. simpl. unfold renameVal at 1. rewrite <- (proj1 applyComposeRenaming). unfold renameVal. rewrite <- (proj1 applyComposeRenaming). 
auto. 
Qed.

Lemma liftAuxComposeRenamingSubst : forall env''' E env' env'' (r:Renaming env' env'') (s:Subst E env'), liftAuxSubst env''' (composeRenamingSubst r s) = composeRenamingSubst (liftAuxRenaming env''' r) (liftAuxSubst env''' s).
induction env'''. auto. 
intros. simpl. rewrite IHenv'''. apply MapExtensional. intros t0 var. dependent induction var; auto. 
simpl. unfold composeRenamingSubst. unfold liftSubst. simpl. unfold renameVal at 1. rewrite <- (proj1 applyComposeRenaming). unfold renameVal. rewrite <- (proj1 applyComposeRenaming). 
auto. 
Qed.

Lemma applyComposeRenamingSubst :
   (forall E t (v:Value E t) env' env'' (r:Renaming env' env'') (s : Subst E env'),
    substVal (composeRenamingSubst r s) v = renameVal r (substVal s v))
/\ (forall E t (e:Exp   E t) env' env'' (r:Renaming env' env'') (s : Subst E env'),
    substExp (composeRenamingSubst r s) e = renameExp r (substExp s e)).
Proof.
apply ExpVal_ind;
(intros; try (autorewrite with substHints renameHints using try rewrite liftComposeRenamingSubst; try rewrite liftComposeRenamingSubst; 
  try rewrite liftAuxComposeRenamingSubst; try rewrite H; try rewrite H0; try rewrite H1); auto).
Qed.

(*==========================================================================
  Composition of substitutions
  ==========================================================================*)

Definition composeSubst env env' env'' (s' : Subst env' env'') (s : Subst env env') : Subst env env'' := fun ty var => substVal s' (s _ var). 

Arguments Scope composeSubst [_ _ _ Subst_scope Subst_scope]. 

Lemma liftComposeSubst : forall env env' env'' ty (s' : Subst env' env'') (s : Subst env env'), liftSubst ty (composeSubst s' s) = composeSubst (liftSubst ty s') (liftSubst ty s).
intros. apply MapExtensional. intros t0 var. dependent destruction var. auto.
unfold composeSubst. simpl. 
rewrite <- (proj1 applyComposeRenamingSubst). unfold composeRenamingSubst. unfold substVal. 
rewrite <- (proj1 applyComposeRenaming). auto.
Qed.

Lemma liftAuxComposeSubst : forall env''' env env' env'' (s' : Subst env' env'') (s : Subst env env'), liftAuxSubst env''' (composeSubst s' s) = composeSubst (liftAuxSubst env''' s') 
  (liftAuxSubst env''' s).
induction env'''. auto. intros. simpl. rewrite IHenv'''. rewrite liftComposeSubst. auto. 
Qed.

Lemma substComposeSubst : 
   (forall env ty (v : Value env ty) env' env'' (s' : Subst env' env'') (s : Subst env env'),
    substVal (composeSubst s' s) v = substVal s' (substVal s v))
/\ (forall env ty (e : Exp   env ty) env' env'' (s' : Subst env' env'') (s : Subst env env'),
    substExp (composeSubst s' s) e = substExp s' (substExp s e)).
Proof.
apply ExpVal_ind;
(intros; try (autorewrite with substHints using try rewrite liftComposeSubst; try rewrite liftComposeSubst; try rewrite liftAuxComposeSubst; try rewrite H; try rewrite H0; try rewrite H1); auto).
Qed.

Lemma composeCons : forall env env' env'' ty (s':Subst env' env'') (s:Subst env env') (v:Value _ ty), 
  composeSubst (consMap v s') (liftSubst ty s) = consMap v (composeSubst s' s).
intros. apply MapExtensional. intros t0 var.  dependent destruction var. auto. 
unfold composeSubst. simpl. unfold substVal. rewrite <- (proj1 applyComposeRenaming). unfold composeRenaming. simpl.
assert ((fun (t0:Ty) (var0:Var env' t0) => s' t0 var0) = s') by (apply MapExtensional; auto). 
rewrite H. auto. 
Qed.

Lemma composeSubstIdLeft : forall env env' (s : Subst env env'), composeSubst (idSubst _) s = s.
Proof. intros. apply MapExtensional. intros. unfold composeSubst. apply (proj1 applyIdSubst). Qed.

Lemma composeSubstIdRight : forall env env' (s:Subst env env'), composeSubst s (idSubst _) = s.
Proof. intros. apply MapExtensional. auto.  
Qed.

(*==========================================================================
  Constructors are injective 
  ==========================================================================*)

Lemma PAIR_injective : 
  forall env ty1 ty2 (v1 : Value env ty1) (v2 : Value env ty2) v3 v4, 
  PAIR v1 v2 = PAIR v3 v4 -> 
  v1 = v3 /\ v2 = v4.
intros. dependent destruction H. auto. 
Qed.

Lemma FST_injective : 
  forall env ty1 ty2 (v1 : Value env (ty1 ** ty2)) v2, 
  FST v1 = FST v2 -> 
  v1 = v2.
intros. dependent destruction H. auto. 
Qed.

Lemma SND_injective : 
  forall env ty1 ty2 (v1 : Value env (ty1 ** ty2)) v2, 
  SND v1 = SND v2 -> 
  v1 = v2.
intros. dependent destruction H. auto. 
Qed.

Lemma VAL_injective : 
  forall env ty (v1 : Value env ty) v2, 
  VAL v1 = VAL v2 -> 
  v1 = v2.
intros. dependent destruction H. auto. 
Qed.

Lemma FIX_injective : 
  forall env ty1 ty2 (e1 : Exp (ty1 :: _ :: env) ty2) e2,
  FIX e1 = FIX e2 -> 
  e1 = e2.
intros. dependent destruction H. auto. 
Qed.

(*==========================================================================
  Closed forms
  ==========================================================================*)
Lemma ClosedFunction : forall ty1 ty2 (v : CValue (ty1 --> ty2)), exists b, v = FIX b.
unfold CValue.
intros ty1 ty2 v.
dependent destruction v.
(* VAR case: impossible *)
dependent destruction v.
(* FIX case *)
exists e. trivial.
Qed.

Lemma ClosedPair : forall ty1 ty2 (v : CValue (ty1 ** ty2)), exists v1, exists v2, v = PAIR v1 v2.
unfold CValue.
intros ty1 ty2 v.
dependent destruction v.
(* VAR case: impossible *)
dependent destruction v.
(* PAIR case *)
exists v1. exists v2. trivial.
Qed.

Lemma ClosedInt : forall (v : CValue Int), exists i, v = INT i. 
unfold CValue.
intros v. dependent destruction v.
exists n. trivial.
dependent destruction v.
Qed.

Lemma ClosedBool : forall (v : CValue Bool), exists b, v = BOOL b. 
unfold CValue.
intros v. dependent destruction v.
exists b. trivial.
dependent destruction v.
Qed.

Unset Implicit Arguments.
