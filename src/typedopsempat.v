(* typedopsem.v
   Standard operational semantics 
*)
Require Import utility.
Require Import Coq.Program.Equality.
Require Import EqdepFacts. 
Require Import typedlambdapat.

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

Definition deconstructPair : forall ty1 ty2 (v : CValue (ty1 ** ty2)), CValue ty1 * CValue ty2.
unfold CValue.
intros.
dependent destruction v.
dependent destruction v.
exact (v1, v2). 
Defined.

Definition deconstructSum : forall ty1 ty2 (v : CValue (Sum ty1 ty2)), CValue ty1 + CValue ty2.
unfold CValue.
intros.
dependent destruction v.
dependent destruction v.
exact (inl _ v).
exact (inr _ v). 
Defined.

Definition castSubst env env' env'' (s : option (Subst (env'' ++ (env' ++ env)) nil)) : option (Subst ((env'' ++ env') ++ env) nil).
intros.
rewrite app_ass. exact s.
Defined.

Implicit Arguments castSubst [env env' env''].

Lemma castSubstEq : forall env env' env'' s1 s2, @castSubst env env' env'' s1 = castSubst s2 -> s1 = s2.
Proof.
intros. destruct s1.  destruct s2. assert (s = s0). apply MapExtensional.
intros t var. inversion var. subst. rewrite <- H1 in var. redestruct env''.  unfold castSubst in H. dependent destruction var.  auto. 
case s1. 
case_eq s2. intros s2' s2'eq. subst. case_eq s1. intros s1' s1'eq. subst. assert (s1' = s2'). unfold castSubst in H. unfold eq_rect_r in H. 
unfold eq_rect in H. case_eq (sym_eq (app_ass env'' env' env)).  intros. destruct H.  auto. case H.  auto. dependent destruction H. apply H. intros s1' s2'. unfold castSubst in H.
unfold eq_rect_r in H.
unfold eq_rect in H.
dcase (sym_eq (app_ass env'' env' env)).  inversion H.  simpl in H.
SearchAbout eq_rect.
assert (EQ := eq_rect_eq). 


 simpl_eq H. elim_eq_rect H. unfold eq_rect_r in H.  dependent destruction H.  auto. destruct H.  case H. 

Fixpoint bindPat env' env (s : Subst env nil) ty (p : Pat env' ty) : CValue ty -> option (Subst (env' ++ env) nil) :=
match p with
| PVAR _ => fun v => Some (consMap v s)
| PWILD _ => fun v => Some s
| PFAIL _ => fun v => None
| PPAIR env1 env2 ty1 ty2 p1 p2 => fun v => 
  let (v1, v2) := deconstructPair v 
  in
    match @bindPat env2 _ s ty2 p2 v2 with
    | None => None
    | Some s' => castSubst (@bindPat env1 _ s' ty1 p1 v1)
    end

| PAS _ _ p => fun v => 
  match bindPat s p v with
  | None => None
  | Some s' => Some (consMap v s')
  end

| PINL _ _ _ p' => fun v =>
  match deconstructSum v with
  | inl v' => bindPat s p' v'
  | inr _ => None
  end

| PINR _ _ _ p' => fun v => 
  match deconstructSum v with
  | inl _ => None
  | inr v' => bindPat s p' v'
  end
end.

Implicit Arguments bindPat [env' env ty]. 

Program Fixpoint appendSubst env1 env2 (s1 : Subst env1 nil) (s2 : Subst env2 nil) : Subst (env1 ++ env2) nil :=
  match env1 (*as env1 return Subst (env1 ++ env2) nil *) with
  | nil => s2
  | ty1::env1' => consMap (hdMap (t:=ty1) (E:=env1') s1) (appendSubst (tlMap (t:=ty1) s1) s2)
  end.

Implicit Arguments appendSubst [env1 env2].

Notation "s1 ++ s2" := (appendSubst s1 s2) : Subst_scope. 
Arguments Scope appendSubst [_ _ Subst_scope Subst_scope]. 

Reserved Notation "v 'matches' p 'by' s" (at level 70, no associativity).

Inductive EvPat : forall ty (env:Env), CValue ty -> Pat env ty -> Subst env nil -> Prop :=
| p_Var : forall ty (v:CValue ty), 
           v matches PVAR ty by [v]
| p_Pair : forall ty1 ty2 env1 env2 v1 v2 (p1:Pat env1 ty1) (p2:Pat env2 ty2) s1 s2, 
           v1 matches p1 by s1 -> v2 matches p2 by s2 -> PAIR v1 v2 matches PPAIR p1 p2 by (s1 ++ s2)
| p_Wild : forall ty v, 
           v matches PWILD ty by idSubst _
| p_As   : forall ty env v (p:Pat env ty) s,
           v matches p by s -> v matches (PAS p) by consMap v s
| p_Inl  : forall ty1 ty2 env v (p:Pat env ty1) s,
           v matches p by s -> INL ty2 v matches PINL _ p by s
| p_Inr  : forall ty1 ty2 env v (p:Pat env ty2) s,
           v matches p by s -> INR ty1 v matches PINR _ p by s
where "v 'matches' p 'by' s" := (EvPat v p s).

Definition castExp : forall env ty, Exp env ty -> Exp (env++nil)%list ty.
intros.
rewrite <- app_nil_end. exact H.
Defined.

Inductive Ev: forall ty, CExp ty -> CValue ty -> Prop :=
| e_Val     : forall ty (v : CValue ty), VAL v =>> v
| e_Op      : forall op n1 n2, OP op (INT n1) (INT n2) =>> INT (op n1 n2)
| e_Gt      : forall n1 n2, GT (INT n1) (INT n2) =>> BOOL (ble_nat n2 n1)
| e_Fst     : forall ty1 ty2 (v1 : CValue ty1) (v2 : CValue ty2), FST (PAIR v1 v2) =>> v1
| e_Snd     : forall ty1 ty2 (v1 : CValue ty1) (v2 : CValue ty2), SND (PAIR v1 v2) =>> v2
| e_App     : forall ty1 ty2 e (v1 : CValue ty1) (v2 : CValue ty2), substExp [ v1, FIX e ] e =>> v2 -> APP (FIX e) v1 =>> v2
| e_Let     : forall ty1 ty2 e1 e2 (v1 : CValue ty1) (v2 : CValue ty2), e1 =>> v1 -> substExp [ v1 ] e2 =>> v2 -> LET e1 e2 =>> v2
| e_LetPat  : forall ty1 ty2 env e1 (p : Pat env ty1) e2 v1 (v2 : CValue ty2), 
              e1 =>> v1 -> forall s, v1 matches p by s -> substExp s e2 =>> v2 -> LETPAT e1 p (castExp e2) =>> v2
| e_IfTrue  : forall ty (e1 e2 : CExp ty) v, e1 =>> v -> COND (BOOL true) e1 e2 =>> v
| e_IfFalse : forall ty (e1 e2 : CExp ty) v, e2 =>> v -> COND (BOOL false) e1 e2 =>> v
where "e '=>>' v" := (Ev e v).

(*==========================================================================
  Determinacy of evaluation
  ==========================================================================*)

Lemma PatDeterminacy: forall ty env (p : Pat env ty) v s1, v matches p by s1 -> forall s2, v matches p by s2 -> s1 = s2.
admit.
Qed.

Lemma Determinacy: forall ty, forall (e : CExp ty) v1, e =>> v1 -> forall v2, e =>> v2 -> v1 = v2.
Proof.
intros ty e v1 Ev1. 
induction Ev1.

(* e_Val *)
intros v2 Ev2. dependent destruction Ev2; trivial. 
(* e_Op *)
intros v2 Ev2. dependent destruction Ev2; trivial.
(* e_Gt *)
intros v2 Ev2. dependent destruction Ev2; trivial.
(* e_Fst *)
intros v3 Ev3. dependent destruction Ev3; trivial.
(* e_Snd *)
intros v3 Ev3. dependent destruction Ev3; trivial.
(* e_App *)
intros v3 Ev3. dependent destruction Ev3; auto.  
(* e_Let *)
intros v3 Ev3. dependent destruction Ev3. rewrite (IHEv1_1 _ Ev3_1) in *. auto. 
(* e_LetPat *)
intros v3 Ev3. dependent destruction Ev3. rewrite (IHEv1_1 _ Ev3_1) in *. assert (s = s0). apply (PatDeterminacy H H0). subst.  clear H H0.
assert (e2 = e3). unfold castExp in H1. dependent destruction H1. rewrite <- app_nil_end in H. destruct H1.    simpl in H1. auto. dependent destruction H1. apply IHEv1_2. ; auto. rewrite H in H0. inversion H0.   subst. auto. 
(* e_IfTrue *) 
intros v3 Ev3. dependent destruction Ev3; auto. 
(* e_IfFalse *)
intros v3 Ev3. dependent destruction Ev3; auto.
Qed.

Unset Implicit Arguments.
