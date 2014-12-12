(*==========================================================================
  Variables
  ==========================================================================*)

Require Import List.
Require Import Program.Equality.
Set Implicit Arguments.
Unset Strict Implicit.
Set Printing Implicit Defensive.

Section Vars.

Variable Ty : Type.

Definition Env := list Ty.

Inductive Var : Env -> Ty -> Type := 
| ZVAR : forall env ty, Var (ty :: env) ty
| SVAR : forall env ty ty', Var env ty -> Var (ty' :: env) ty.

(*==========================================================================
  Variable-domain maps. 
  By instantiating P with Var we get renamings.
  By instantiating P with terms we get substitutions.
  ==========================================================================*)

Definition Map (P : Env -> Ty -> Type) env env' := forall t, Var env t -> P env' t.

(* Head, tail and cons *)
Definition tlMap P env env' ty (m : Map P (ty :: env) env') : Map P env env' := fun ty' v => m ty' (SVAR ty v).
Definition hdMap P env env' ty (m : Map P (ty :: env) env') : P env' ty := m ty (ZVAR _ _).
Implicit Arguments tlMap [P env env' ty].
Implicit Arguments hdMap [P env env' ty].

Program Definition consMap P env env' ty (v : P env' ty) (m:Map P env env') : Map P (ty :: env) env' :=
    fun ty' (var:Var (ty :: env) ty') => 
    match var with
    | ZVAR _ _ => v
    | SVAR _ _ _ var => m _ var
    end.
Implicit Arguments consMap [P env env' ty].

Axiom MapExtensional : forall P env env' (r1 r2 : Map P env env'), (forall ty var, r1 ty var = r2 ty var) -> r1 = r2.

Lemma hdConsMap : forall P env env' ty (v : P env' ty) (s : Map P env env'), hdMap (consMap v s) = v. Proof. auto. Qed.
Lemma tlConsMap : forall P env env' ty (v : P env' ty) (s : Map P env env'), tlMap (consMap v s) = s. Proof. intros. apply MapExtensional. auto. Qed.

Lemma consMapInv : forall P env env' ty (m:Map P (ty :: env) env'), exists m', exists v, m = consMap v m'.  
intros. exists (tlMap m). exists (hdMap m).
apply MapExtensional. dependent destruction var; auto. 
Qed.

Definition Renaming := Map Var.

Definition idRenaming env : Renaming env env := fun ty (var : Var env ty) => var.
Implicit Arguments idRenaming [].

Definition composeRenaming P env env' env'' (m : Map P env' env'') (r : Renaming env env') : Map P env env'' := fun t var => m _ (r _ var). 


Lemma composeRenamingAssoc : 
  forall P env env' env'' env''' (m : Map P env'' env''') r' (r : Renaming env env'), 
  composeRenaming m (composeRenaming r' r) = composeRenaming (composeRenaming m r') r.
Proof. auto. Qed.

Lemma composeRenamingIdLeft : forall env env' (r : Renaming env env'), composeRenaming (idRenaming _) r = r.
Proof. intros. apply MapExtensional. auto. Qed.

Lemma composeRenamingIdRight : forall P env env' (m:Map P env env'), composeRenaming m (idRenaming _) = m.
Proof. intros. apply MapExtensional. auto. Qed.

End Vars.


