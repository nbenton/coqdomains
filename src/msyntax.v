(**********************************************************************************
 * msyntax.v                                                                      *
 * Formalizing Domains, Ultrametric Spaces and Semantics of Programming Languages *
 * Nick Benton, Lars Birkedal, Andrew Kennedy and Carsten Varming                 *
 * July 2010                                                                      *
 * Build with Coq 8.2pl1 plus SSREFLECT                                           *
 **********************************************************************************)

(* The kitchen sink language: polymorphic cbv lambda calculus with higher order store
   and recursive types
   Presentation of the syntax is just a tad longwinded at the moment...
*)

Require Export ssreflect ssrnat ssrbool eqtype ssrfun Finmap.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(** * PolyFPC with refs *)
(** ** Types and contexts *)
(** We define PCF types as an inductive type Ty *)
(*=Ty *)  
Inductive Ty (n:nat) : Type :=
  | TVar i: i < n -> Ty n 
  | Int: Ty n | Unit: Ty n
  | Product: Ty n -> Ty n -> Ty n
  | Sum: Ty n -> Ty n -> Ty n
  | Mu: Ty (S n) -> Ty n 
  | All: Ty (S n) -> Ty n
  | Arrow: Ty n -> Ty n -> Ty n 
  | Ref: Ty n -> Ty n.
(*=End *)  

(* Equality on Ty is deciable and thus equality proofs on Ty
   are unique.
   Carsten
 *)

Implicit Arguments Unit [n].
Implicit Arguments Int [n].

Fixpoint TyEq n (x y:Ty n) : bool :=
match x,y with
| TVar i l, TVar j l' => i == j
| Int, Int => true
| Unit, Unit => true
| Product x y, Product x' y' => TyEq x x' && TyEq y y'
| Sum x y, Sum x' y' => TyEq x x' && TyEq y y'
| Mu x, Mu y => TyEq x y
| All x, All y => TyEq x y
| Arrow x y, Arrow x' y' => TyEq x x' && TyEq y y'
| Ref x, Ref y => TyEq x y
| _,_ => false
end.

Lemma TyEqP n : Equality.axiom (@TyEq n).
move => x y. apply: (iffP idP) => [|<-].
- elim: n / x y => n.
  + move => i l y.
    by case: y ; first by simpl ; move => i' l' e ; move: l' ; rewrite <- (eqnP e) ; clear ; move => l' ; rewrite (eq_irrelevance l l').
  + by case.
  + by case.
  + move => t0 IH0 t1 IH1. by case ; try done ; simpl ; move => t0' t1' X ; rewrite (IH0 _ (proj1 (andP X))) ;
    by rewrite (IH1 _ (proj2 (andP X))).
  + move => t0 IH0 t1 IH1. by case ; try done ; simpl ; move => t0' t1' X ; rewrite (IH0 _ (proj1 (andP X))) ;
    by rewrite (IH1 _ (proj2 (andP X))).
  + move => t IH. by case ; try done ; move => t' X ; rewrite (IH _ X).
  + move => t IH. by case ; try done ; move => t' X ; rewrite (IH _ X).
  + move => t0 IH0 t1 IH1. by case ; try done ; simpl ; move => t0' t1' X ; rewrite (IH0 _ (proj1 (andP X))) ;
    by rewrite (IH1 _ (proj2 (andP X))).
  + move => t IH. by case ; try done ; move => t' X ; rewrite (IH _ X).
- clear. elim: n / x => n; simpl ; try done ; try by move => x [->] y [->].
Qed.

Canonical Structure Ty_eqMixin n := EqMixin (@TyEqP n).
Canonical Structure Ty_eqType n := Eval hnf in EqType _ (@Ty_eqMixin n).

Lemma Ty_eq_unique n : forall (t t' : Ty n) (p p':t = t'), p = p'.
exact: eq_irrelevance.
Qed.

(* begin hide *)

Notation "a --> b" := (Arrow a b) (at level 55, right associativity).
Notation "a ** b" := (Product a b) (at level 55).

(* end hide *)
(** printing --> %\ensuremath{\longrightarrow}% *)
(** printing ** %\ensuremath{\times}% *)
(** printing Sum %\ensuremath{+}% *)

Definition TypeEnv n := seq (Ty n).

Fixpoint tshiftR k m n (t:Ty n) : Ty (addn n m) :=
match t with
| TVar i l => if i < k then @TVar _ i (ssrnat.leq_trans l (leq_addr _ _)) else @TVar _ (i+m) (leq_add l (leqnn _) : (i+m < n + m))
| Int => Int
| Unit => Unit
| Product t t' => Product (tshiftR k m t) (tshiftR k m t')
(* | Void => Void*)
| Sum t t' => Sum (tshiftR k m t) (tshiftR k m t')
| Mu t => Mu (tshiftR (S k) m t)
| All t => All (tshiftR (S k) m t)
| Arrow t t' => Arrow (tshiftR k m t) (tshiftR k m t')
| Ref t => Ref (tshiftR k m t)
end.

Definition tshiftL k m n (t:Ty n) : Ty (m+n) := eq_rect _ Ty (tshiftR k m t) _ (addnC n m).

Fixpoint tsubst n (s:seq (Ty n)) m (t:Ty m) : Ty n :=
match t with
| TVar i l => nth Unit s i
| Int => Int
| Unit => Unit
| Product t t' => Product (tsubst s t) (tsubst s t')
(*| Void => Void*)
| Sum t t' => Sum (tsubst s t) (tsubst s t')
| Mu t => Mu (tsubst (TVar (ltn0Sn _) :: (map (@tshiftL 0 1 n) s)) t)
| All t => All (tsubst (TVar (ltn0Sn _) :: (map (@tshiftL 0 1 n) s)) t)
| Arrow t t' => Arrow (tsubst s t) (tsubst s t')
| Ref t => Ref (tsubst s t)
end.

Fixpoint nth_error A (l:seq A) (n:nat) : option A :=
match l with 
| (x::xr) => match n with O => Some x | S n => nth_error xr n end
| nil => None
end.

Lemma nth_error_nth A (l:seq A) n : nth_error l n = nth None (map (@Some _) l) n.
elim: l n ; first by case ; by [].
move => x xr IH. case ; first by [].
move => n. simpl. by apply (IH n).
Qed.

Fixpoint idsubr i j (l:seq (Ty i)) (p:j <= i) {struct j} :=
match j as j0 return j0 <= i -> seq (Ty i) with
| O => fun _ => l
| S j => fun p => @idsubr i j (@TVar i j p :: l) (ltnW p)
end p.

Definition idsub n i : seq (Ty (n+i)) := @idsubr (n+i) i nil (leq_addl _ _).

Lemma nth_error_map T T' (f:T -> T') (l:seq T) i : nth_error (map f l) i = option_map f (nth_error l i).
elim: l i ; first by [].
move => e l IH. case ; first by [].
by apply IH.
Qed.

Lemma tshiftRC n (t:Ty n) k i k' i' (a:(n + i + i') = (n + i' + i)) : k <= k' ->
     eq_rect _ Ty (tshiftR (k'+i) i' (tshiftR k i t)) _ a = tshiftR k i (tshiftR k' i' t).
elim: n / t k i k' i' a.
- move => n i l k j k' j' e lk. simpl.
  case_eq (i < k) => ik. simpl.
  + rewrite (ssrnat.leq_trans ik lk). simpl. rewrite ik.
    rewrite (ssrnat.leq_trans ik (ssrnat.leq_trans lk (leq_addr j k'))).
    have a:=(ssrnat.leq_trans (ssrnat.leq_trans l (leq_addr j n)) (leq_addr j' (n + j))).
    rewrite (eq_irrelevance (ssrnat.leq_trans (ssrnat.leq_trans l (leq_addr j n)) (leq_addr j' (n + j))) a).
    move: a. generalize e. rewrite e. clear e. move => e. rewrite (eq_irrelevance e (refl_equal _)). simpl.
    move => a. by rewrite <- (eq_irrelevance a (ssrnat.leq_trans (ssrnat.leq_trans l (leq_addr j' n)) (leq_addr j (n + j')))).
  + case_eq (i < k') => ik'.
    * simpl. rewrite (ltn_add2r j i k'). rewrite ik'. rewrite ik.
      have a:=(ssrnat.leq_trans (leq_add l (leqnn j)) (leq_addr j' (n + j))).
      rewrite (eq_irrelevance (ssrnat.leq_trans (leq_add l (leqnn j)) (leq_addr j' (n + j))) a).
      move: a. generalize e. rewrite e. clear e. move => e. rewrite (eq_irrelevance e (refl_equal _)). simpl.
      move => a. by rewrite (eq_irrelevance (leq_add (ssrnat.leq_trans l (leq_addr j' n)) (leqnn j)) a).
    * simpl. rewrite (ltn_add2r j i k'). rewrite ik'.
      rewrite ltnNge  in ik. have ii:=ssrnat.leq_trans (negbFE ik) (leq_addr j' _).
      rewrite ltnNge. rewrite (negbF ii).
      have a:=(leq_add (leq_add  l (leqnn j)) (leqnn j')). rewrite (eq_irrelevance (leq_add (leq_add  l (leqnn j)) (leqnn j')) a).
      move: a. generalize e. rewrite e. clear e. move => e. rewrite (eq_irrelevance e (refl_equal _)). simpl. clear.
      move => a. have a':=(leq_add (leq_add l (leqnn j')) (leqnn j)). pose b:=a :  i + j + j' < n + j' + j.
      have e:a = b by []. rewrite e. 
      rewrite (eq_irrelevance (leq_add (leq_add l (leqnn j')) (leqnn j)) a'). clear e.
      have e:i + j + j' = i + j' + j. do 2 rewrite <- addnA. by rewrite (addnC j).
      move: b. rewrite e. clear e a. move => b. by rewrite (eq_irrelevance a' b).
- move => n k i k' i' a l. simpl. generalize a. rewrite a. clear a. move => a. by rewrite (eq_irrelevance a (refl_equal _)).
- move => n k i k' i' a l. simpl. generalize a. rewrite a. clear a. move => a. by rewrite (eq_irrelevance a (refl_equal _)).
- move => n t0 IH0 t1 IH1 k i k' i' a l. simpl. rewrite <- (IH0 _ _ _ _ a l). rewrite <- (IH1 _ _ _ _ a l).
  clear IH0 IH1. simpl. generalize a. rewrite <- a. clear a. move => a. by rewrite (eq_irrelevance a (refl_equal _)).
(* - move => n k i k' i' a l. simpl. generalize a. rewrite a. clear a. move => a. by rewrite (nat_eq_unique a (refl_equal _)).*)
- move => n t0 IH0 t1 IH1 k i k' i' a l. simpl. rewrite <- (IH0 _ _ _ _ a l). rewrite <- (IH1 _ _ _ _ a l).
  clear IH0 IH1. simpl. generalize a. rewrite <- a. clear a. move => a. by rewrite (eq_irrelevance a (refl_equal _)).
- simpl. move => n t IH k i k' i' a l. specialize (IH (k.+1) i (k'.+1) i').
  have a':(n + i + i').+1 = (n + i' + i).+1 by rewrite a. specialize (IH a' l).
  apply: (trans_eq _ (f_equal (@Mu _) IH)). have e:(n.+1 + i' + i) = (n + i' + i).+1 by [].
  apply trans_eq with (y:=Mu (eq_rect (n + i + i').+1 Ty (tshiftR (k'.+1 + i) i' (tshiftR k.+1 i t)) (n + i' + i).+1 a')) ; last by [].
  clear IH.
  move: a a'. unfold addn. unfold addn_rec. fold plus. move => a. generalize a. rewrite <- a. simpl.
  clear a e. move => a a'. rewrite (eq_irrelevance a (refl_equal _)). by rewrite (eq_irrelevance a' (refl_equal _)).
- simpl. move => n t IH k i k' i' a l. specialize (IH (k.+1) i (k'.+1) i').
  have a':(n + i + i').+1 = (n + i' + i).+1 by rewrite a. specialize (IH a' l).
  apply: (trans_eq _ (f_equal (@All _) IH)). have e:(n.+1 + i' + i) = (n + i' + i).+1 by [].
  apply trans_eq with (y:=All (eq_rect (n + i + i').+1 Ty (tshiftR (k'.+1 + i) i' (tshiftR k.+1 i t)) (n + i' + i).+1 a')) ; last by [].
  clear IH.
  move: a a'. unfold addn. unfold addn_rec. fold plus. move => a. generalize a. rewrite <- a. simpl.
  clear a e. move => a a'. rewrite (eq_irrelevance a (refl_equal _)). by rewrite (eq_irrelevance a' (refl_equal _)).
- move => n t0 IH0 t1 IH1 k i k' i' a l. simpl. rewrite <- (IH0 _ _ _ _ a l). rewrite <- (IH1 _ _ _ _ a l).
  clear IH0 IH1. simpl. generalize a. rewrite <- a. clear a. move => a. by rewrite (eq_irrelevance a (refl_equal _)).
- move => n t IH k i k' i' a l. simpl. rewrite <- (IH _ _ _ _ a l). 
  simpl. generalize a. rewrite <- a. clear a. move => a. by rewrite (eq_irrelevance a (refl_equal _)).
Qed.

Lemma tshiftR_tshiftR n (t:Ty n) k i j : tshiftR k i (tshiftR k j t) = eq_rect _ Ty (tshiftR k (j+i) t) _ (addnA _ _ _).
elim: n / t k i j.
- move => n i l k m j. simpl. case_eq (i < k) ; move => L.
  + have e:=(ssrnat.leq_trans l (leq_addr j n)). rewrite (eq_irrelevance (ssrnat.leq_trans l (leq_addr j n)) e).
    have e':=(ssrnat.leq_trans l (leq_addr (j + m) n)). rewrite (eq_irrelevance (ssrnat.leq_trans l (leq_addr (j + m) n)) e').
    have a:=addnA n j m. rewrite (eq_irrelevance (addnA n j m) a).
    move: e'. generalize a. rewrite a. clear a. move => a. rewrite (eq_irrelevance a (refl_equal _)). simpl. clear a.
    rewrite L. move => e'. by rewrite (eq_irrelevance (ssrnat.leq_trans e (leq_addr m (n + j))) e').
  + have e:=((leq_add l (leqnn j)) : i + j < n + j). rewrite (eq_irrelevance  ((leq_add l (leqnn j))) e).
    have e':=(leq_add l (leqnn (j + m)) : i + (j + m) < n + (j + m)). rewrite (eq_irrelevance (leq_add l (leqnn (j + m))) e').
    have a:=(addnA n j m). rewrite (eq_irrelevance (addnA n j m) a).
    move: e'. generalize a. rewrite a. clear a. move => a. rewrite (eq_irrelevance a (refl_equal _)). simpl. clear a.  
    rewrite ltnNge in L. have LL:=negbFE  L. clear L. have L:=ssrnat.leq_trans LL (leq_addr j i).
    have x:=leqP k (i+j). rewrite L in x.
    move: x. case ; last by move => F ; have FF:=(leq_ltn_trans L F) ; rewrite (ltnn k) in FF.
    move => _ e'. have a:(i + j) + m = i + (j + m) by rewrite addnA.
    move: e e'. rewrite <- a. clear a. move => e e'. by rewrite (eq_irrelevance (leq_add e (leqnn m)) e').
- move => n k i j. simpl. have a:=(addnA n j i). rewrite (eq_irrelevance (addnA n j i) a).
  generalize a. rewrite a. clear a. move => a. by rewrite (eq_irrelevance a (refl_equal _)).
- move => n k i j. simpl. have a:=(addnA n j i). rewrite (eq_irrelevance (addnA n j i) a).
  generalize a. rewrite a. clear a. move => a. by rewrite (eq_irrelevance a (refl_equal _)).
- move => n t0 IH0 t1 IH1 k i j. simpl. rewrite IH0. rewrite IH1. clear IH0 IH1.
  have a:=(addnA n j i). rewrite (eq_irrelevance (addnA n j i) a).
  generalize a. rewrite <- a. clear a. move => a. by rewrite (eq_irrelevance a (refl_equal _)).
(*- move => n k i j. simpl. have a:=(addnA n j i). rewrite (nat_eq_unique (addnA n j i) a).
  generalize a. rewrite a. clear a. move => a. by rewrite (nat_eq_unique a (refl_equal _)).*)
- move => n t0 IH0 t1 IH1 k i j. simpl. rewrite IH0. rewrite IH1. clear IH0 IH1.
  have a:=(addnA n j i). rewrite (eq_irrelevance (addnA n j i) a).
  generalize a. rewrite <- a. clear a. move => a. by rewrite (eq_irrelevance a (refl_equal _)).
- move => n t IH k i j. simpl. rewrite IH. clear IH. have a:=(addnA (S n) j i).
  rewrite (eq_irrelevance (addnA _ j i) a).
  apply trans_eq with (y:=@Mu (addn (addn n j) i) (eq_rect (n + (j + i)).+1 Ty (tshiftR (k.+1) (j + i) t) (n + j + i).+1 a)) ; first by [].
  have a':=a. do 3 rewrite addSn in a'. rewrite (eq_irrelevance a a'). clear a.
  have a:=addnA n j i. rewrite (eq_irrelevance (addnA n j i) a).
  apply trans_eq with (y:=eq_rect (addn n (addn j i)) Ty (@Mu (addn n (addn j i)) (tshiftR (k.+1) (j + i) t)) (n + j + i) a) ; last by [].
  move: a'. generalize a. rewrite <- a. clear a.
  move => a a'. rewrite (eq_irrelevance a (refl_equal _)). by rewrite (eq_irrelevance a' (refl_equal _)).
- move => n t IH k i j. simpl. rewrite IH. clear IH. have a:=(addnA (S n) j i).
  rewrite (eq_irrelevance (addnA _ j i) a).
  apply trans_eq with (y:=@All (addn (addn n j) i) (eq_rect (n + (j + i)).+1 Ty (tshiftR (k.+1) (j + i) t) (n + j + i).+1 a)) ; first by [].
  have a':=a. do 3 rewrite addSn in a'. rewrite (eq_irrelevance a a'). clear a.
  have a:=addnA n j i. rewrite (eq_irrelevance (addnA n j i) a).
  apply trans_eq with (y:=eq_rect (addn n (addn j i)) Ty (@All (addn n (addn j i)) (tshiftR (k.+1) (j + i) t)) (n + j + i) a) ; last by [].
  move: a'. generalize a. rewrite <- a. clear a.
  move => a a'. rewrite (eq_irrelevance a (refl_equal _)). by rewrite (eq_irrelevance a' (refl_equal _)).
- move => n t0 IH0 t1 IH1 k i j. simpl. rewrite IH0. rewrite IH1. clear IH0 IH1.
  have a:=(addnA n j i). rewrite (eq_irrelevance (addnA n j i) a).
  generalize a. rewrite <- a. clear a. move => a. by rewrite (eq_irrelevance a (refl_equal _)).
- move => n t0 IH0 k i j. simpl. rewrite IH0. clear IH0.
  have a:=(addnA n j i). rewrite (eq_irrelevance (addnA n j i) a).
  generalize a. rewrite <- a. clear a. move => a. by rewrite (eq_irrelevance a (refl_equal _)).
Qed.

Lemma eq_nat_comp n m n' p p' x : eq_rect _ Ty (eq_rect n Ty x m p) n' p' =
                           eq_rect _ Ty x _ (trans_eq p p').
move => n m n' p. generalize p. rewrite p. clear n p. move => p. rewrite (eq_irrelevance p (refl_equal _)). simpl. clear p.
move => p'. by rewrite (eq_irrelevance (trans_eq (refl_equal m) p') p').
Qed.

Lemma tshiftL_tshiftL n (t:Ty n) k i j : tshiftL k i (tshiftL k j t) = eq_rect _ Ty (tshiftL k (i+j) t) _ (sym_eq(addnA _ _ _)).
move => n t k i j. unfold tshiftL.
rewrite eq_nat_comp.
have c:=(addnC (j + n) i). rewrite (eq_irrelevance (addnC (j + n) i) c).
have a:=(trans_eq (addnC n (i + j)) (sym_eq (addnA i j n))).
rewrite (eq_irrelevance (trans_eq (addnC n (i + j)) (sym_eq (addnA i j n))) a).
have c':=(addnC n j). rewrite (eq_irrelevance (addnC n j) c').
move: c a. generalize c'. rewrite <- c'. clear c'.
move => c'. rewrite (eq_irrelevance c' (refl_equal _)). simpl. clear c'.
move => c c'. rewrite tshiftR_tshiftR. rewrite eq_nat_comp.
move: c c'. rewrite (addnC i j). move => c c'.
by rewrite (eq_irrelevance (trans_eq (addnA n j i) c) c').
Qed.

Lemma tsubst_shiftR n (t:Ty n) k i m s' (s:seq (Ty m)) :
    map (@tshiftR k i _) (take k s) = take k s' ->
    map (@tshiftR k i _) (drop k s) = drop (k+i) s' ->
    tsubst s' (tshiftR k i t) = tshiftR k i (tsubst s t).
move => n t. elim: n / t.
- move => n i l k j m s' s m0 m1. simpl.
  case_eq (i < k).
  + move => L. simpl. have f:=f_equal (fun x => nth Unit x i) m0.
    have ll:=f_equal size m0. rewrite size_map in ll.
    case_eq (i < size (take k s)).
    * move => si. have li:i < size s. rewrite size_take in si. move: si. case_eq (k < size s) ; last by [].
                move => l0 _. by apply (ssrnat.ltn_trans L l0).
      rewrite (nth_take _ L) in f. rewrite (nth_map (@Unit _) _ _ si) in f. rewrite (nth_take _ L) in f.
      by rewrite f.
    * move => si. have li:(size s <= i). rewrite size_take in si. move: si. case (k < size s) ; first by rewrite L.
                move => l0. rewrite ltnNge in l0. by apply (negbFE l0).
      rewrite (nth_default _ li). clear li.
      have li:(size s' <= i). rewrite ll in si. rewrite size_take in si. move: si. case (k < size s') ; first by rewrite L.
                move => l0. rewrite ltnNge in l0. by apply (negbFE l0).
      by rewrite (nth_default _ li).
  + move => ll. simpl. have f:=f_equal (fun x => nth Unit x (i - k)) m1. rewrite map_drop in f.
    do 2 rewrite nth_drop in f. have ll':k <= i by rewrite ltnNge in ll ; apply (negbFE ll).
    rewrite (subnKC ll') in f. have e : k + j + (i - k) = i + j by rewrite addnC ; rewrite addnA ; by rewrite subnK.
    rewrite e in f. rewrite <- f.
    case_eq (i < size s) ; first by move => x ; by rewrite (nth_map (@Unit _) _ _ x).
    rewrite ltnNge. move => x. rewrite (nth_default) ; last by rewrite size_map ; apply (negbFE x).
    by rewrite (nth_default _ (negbFE x)).
- by [].
- by [].
- simpl. move => n t0 IH0 t1 IH1 k i m s' s m0 m1. simpl. rewrite (IH0 _ _ _ s' s m0 m1). by rewrite (IH1 _ _ _ s' s m0 m1).
(*- by [].*)
- simpl. move => n t0 IH0 t1 IH1 k i m s' s m0 m1. simpl. rewrite (IH0 _ _ _ s' s m0 m1). by rewrite (IH1 _ _ _ s' s m0 m1).
- move => n t IH k i m s' s m0 m1. simpl.
  specialize (IH (S k) i (S m) (TVar (ltn0Sn (m + i)) :: map (@tshiftL 0 1 _) s')).
  specialize (IH (TVar (n:=m.+1) (i:=0) (ltn0Sn m) :: map (@tshiftL 0 1 _) s)).
  rewrite IH ; first by [] ; clear IH.
  + simpl. rewrite <- map_take. rewrite map_map. rewrite <- map_take. rewrite <- m0. rewrite map_map.
    f_equal ; first by rewrite (eq_irrelevance (ssrnat.leq_trans (ltn0Sn m) (leq_addr i m.+1)) (ltn0Sn (m + i))).
    apply eq_map. move => x. simpl. unfold tshiftL.
    have a:(m + 1 + i) = (m + i + 1) by  do 2 rewrite <- addnA ; f_equal ; rewrite <- addnC.
    rewrite <- (tshiftRC _ a (leq0n _)). rewrite eq_nat_comp. have b:=(addnC m 1). rewrite (eq_irrelevance (addnC m 1) b).
    have c:=(trans_eq a (addnC (m + i) 1)). rewrite (eq_irrelevance (trans_eq a (addnC (m + i) 1)) c). clear a.
    move: b c. unfold addn. unfold addn_rec. simpl. move => b c. have c':((m + 1)%coq_nat + i)%coq_nat = (S m + i) % coq_nat by rewrite c.
    rewrite (eq_irrelevance c c'). clear c.
    apply trans_eq with (y:=eq_rect ((m + 1)%coq_nat + i)%coq_nat (fun t0 : nat => Ty t0)
     (tshiftR (k + 1)%coq_nat i (tshiftR 0 1 x)) (S m + i)%coq_nat c') ; last by [].
    have g: @eq (Ty (S m + i)%coq_nat) (tshiftR k.+1 i
     (eq_rect (m + 1)%coq_nat (fun n0 : nat => Ty n0) 
        (tshiftR 0 1 x) m.+1 b))
   (eq_rect ((m + 1)%coq_nat + i)%coq_nat (fun t0 : nat => Ty t0)
     (tshiftR (k + 1)%coq_nat i (tshiftR 0 1 x)) (m.+1 + i)%coq_nat c') ; last by [].
    move: c'. generalize b. rewrite <- b. clear b. move => b. rewrite (eq_irrelevance b (refl_equal _)). simpl.
    move => c'. rewrite (eq_irrelevance c' (refl_equal _)). simpl.
    have a:= (addnC k 1). unfold addn in a. unfold addn_rec in a. by rewrite a.
  + simpl. rewrite <- map_drop. rewrite map_map. rewrite <- map_drop. fold addn. rewrite <- m1. rewrite map_map.
    apply eq_map. move => x. simpl. unfold tshiftL.
    have a:(m + 1 + i) = (m + i + 1) by  do 2 rewrite <- addnA ; f_equal ; rewrite <- addnC.
    rewrite <- (tshiftRC _ a (leq0n _)). rewrite eq_nat_comp. have b:=(addnC m 1). rewrite (eq_irrelevance (addnC m 1) b).
    have c:=(trans_eq a (addnC (m + i) 1)). rewrite (eq_irrelevance (trans_eq a (addnC (m + i) 1)) c). clear a.
    move: b c. unfold addn. unfold addn_rec. simpl. move => b c. have c':((m + 1)%coq_nat + i)%coq_nat = (S m + i) % coq_nat by rewrite c.
    rewrite (eq_irrelevance c c'). clear c.
    apply trans_eq with (y:=eq_rect ((m + 1)%coq_nat + i)%coq_nat (fun t0 : nat => Ty t0)
     (tshiftR (k + 1)%coq_nat i (tshiftR 0 1 x)) (S m + i)%coq_nat c') ; last by [].
    have g: @eq (Ty (S m + i)%coq_nat) (tshiftR k.+1 i
     (eq_rect (m + 1)%coq_nat (fun n0 : nat => Ty n0) 
        (tshiftR 0 1 x) m.+1 b))
   (eq_rect ((m + 1)%coq_nat + i)%coq_nat (fun t0 : nat => Ty t0)
     (tshiftR (k + 1)%coq_nat i (tshiftR 0 1 x)) (m.+1 + i)%coq_nat c') ; last by [].
    move: c'. generalize b. rewrite <- b. clear b. move => b. rewrite (eq_irrelevance b (refl_equal _)). simpl.
    move => c'. rewrite (eq_irrelevance c' (refl_equal _)). simpl.
    have a:= (addnC k 1). unfold addn in a. unfold addn_rec in a. by rewrite a.
- move => n t IH k i m s' s m0 m1. simpl.
  specialize (IH (S k) i (S m) (TVar (ltn0Sn (m + i)) :: map (@tshiftL 0 1 _) s')).
  specialize (IH (TVar (n:=m.+1) (i:=0) (ltn0Sn m) :: map (@tshiftL 0 1 _) s)).
  rewrite IH ; first by [].
  + simpl. rewrite <- (map_take). rewrite map_map. rewrite <- map_take. rewrite <- m0. rewrite map_map.
    f_equal ; first by rewrite (eq_irrelevance (ssrnat.leq_trans (ltn0Sn m) (leq_addr i m.+1)) (ltn0Sn (m + i))).
    apply eq_map. move => x. simpl. unfold tshiftL.
    have a:(m + 1 + i) = (m + i + 1) by  do 2 rewrite <- addnA ; f_equal ; rewrite <- addnC.
    rewrite <- (tshiftRC _ a (leq0n _)). rewrite eq_nat_comp. have b:=(addnC m 1). rewrite (eq_irrelevance (addnC m 1) b).
    have c:=(trans_eq a (addnC (m + i) 1)). rewrite (eq_irrelevance (trans_eq a (addnC (m + i) 1)) c). clear a.
    move: b c. unfold addn. unfold addn_rec. simpl. move => b c. have c':((m + 1)%coq_nat + i)%coq_nat = (S m + i) % coq_nat by rewrite c.
    rewrite (eq_irrelevance c c'). clear c.
    apply trans_eq with (y:=eq_rect ((m + 1)%coq_nat + i)%coq_nat (fun t0 : nat => Ty t0)
     (tshiftR (k + 1)%coq_nat i (tshiftR 0 1 x)) (S m + i)%coq_nat c') ; last by [].
    have g: @eq (Ty (S m + i)%coq_nat) (tshiftR k.+1 i
     (eq_rect (m + 1)%coq_nat (fun n0 : nat => Ty n0) 
        (tshiftR 0 1 x) m.+1 b))
   (eq_rect ((m + 1)%coq_nat + i)%coq_nat (fun t0 : nat => Ty t0)
     (tshiftR (k + 1)%coq_nat i (tshiftR 0 1 x)) (m.+1 + i)%coq_nat c') ; last by [].
    move: c'. generalize b. rewrite <- b. clear b. move => b. rewrite (eq_irrelevance b (refl_equal _)). simpl.
    move => c'. rewrite (eq_irrelevance c' (refl_equal _)). simpl.   clear IH.
    have a:= (addnC k 1). unfold addn in a. unfold addn_rec in a. by rewrite a.
  + simpl. rewrite <- map_drop. rewrite map_map. rewrite <- map_drop. fold addn. rewrite <- m1. rewrite map_map.
    apply eq_map. move => x. simpl. unfold tshiftL.
    have a:(m + 1 + i) = (m + i + 1) by  do 2 rewrite <- addnA ; f_equal ; rewrite <- addnC. clear IH.
    rewrite <- (tshiftRC _ a (leq0n _)). rewrite eq_nat_comp. have b:=(addnC m 1). rewrite (eq_irrelevance (addnC m 1) b).
    have c:=(trans_eq a (addnC (m + i) 1)). rewrite (eq_irrelevance (trans_eq a (addnC (m + i) 1)) c). clear a.
    move: b c. unfold addn. unfold addn_rec. simpl. move => b c. have c':((m + 1)%coq_nat + i)%coq_nat = (S m + i) % coq_nat by rewrite c.
    rewrite (eq_irrelevance c c'). clear c.
    apply trans_eq with (y:=eq_rect ((m + 1)%coq_nat + i)%coq_nat (fun t0 : nat => Ty t0)
     (tshiftR (k + 1)%coq_nat i (tshiftR 0 1 x)) (S m + i)%coq_nat c') ; last by [].
    have g: @eq (Ty (S m + i)%coq_nat) (tshiftR k.+1 i
     (eq_rect (m + 1)%coq_nat (fun n0 : nat => Ty n0) 
        (tshiftR 0 1 x) m.+1 b))
   (eq_rect ((m + 1)%coq_nat + i)%coq_nat (fun t0 : nat => Ty t0)
     (tshiftR (k + 1)%coq_nat i (tshiftR 0 1 x)) (m.+1 + i)%coq_nat c') ; last by [].
    move: c'. generalize b. rewrite <- b. clear b. move => b. rewrite (eq_irrelevance b (refl_equal _)). simpl.
    move => c'. rewrite (eq_irrelevance c' (refl_equal _)). simpl.
    have a:= (addnC k 1). unfold addn in a. unfold addn_rec in a. by rewrite a.
- simpl. move => n t0 IH0 t1 IH1 k i m s' s m0 m1. simpl. rewrite (IH0 _ _ _ s' s m0 m1). by rewrite (IH1 _ _ _ s' s m0 m1).
- simpl. move => n t IH k i m s' s m0 m1. simpl. by rewrite (IH _ _ _ s' s m0 m1).
Qed.

Lemma tsubst_shiftL n (t:Ty n) k i m s' (s:seq (Ty m)) :
    map (@tshiftR k i _) (take k s) = take k s' ->
    map (@tshiftR k i _) (drop k s) = drop (k+i) s' ->
    tsubst s' (tshiftL k i t) = tshiftR k i (tsubst s t).
move => n t k i m s' s m0 m1.
rewrite <- (tsubst_shiftR _  m0 m1). unfold tshiftL. have a:=(addnC n i). rewrite (eq_irrelevance (addnC n i) a).
generalize a. rewrite <- a. clear a. move => a. by rewrite (eq_irrelevance a (refl_equal _)).
Qed.

Lemma tsubst_eq i (t:Ty i) n m (e:n = m) s : eq_rect _ Ty (tsubst s t) _ e = tsubst (map (fun x => eq_rect _ Ty x _ e) s) t.
move => i t. elim: i / t.
- simpl. move => n i l h k e s.
  case_eq (i < size s) ; move => ll ; first by rewrite (nth_map (@Unit _)).
  rewrite ltnNge in ll. have l0:=negbFE ll.
  rewrite (nth_default _ l0). rewrite nth_default ; last by rewrite size_map.
  generalize e. rewrite e. clear e. move => e. by rewrite (eq_irrelevance e (refl_equal _)).
- simpl. move => _ h k e _. generalize e. rewrite e. clear e. move => e. by rewrite (eq_irrelevance e (refl_equal _)).
- simpl. move => _ h k e _. generalize e. rewrite e. clear e. move => e. by rewrite (eq_irrelevance e (refl_equal _)).
- simpl. move => n t0 IH0 t1 IH1 h k e s. rewrite <- IH0. rewrite <- IH1. move: s.
  generalize e. rewrite e. clear e. move => e. by rewrite (eq_irrelevance e (refl_equal _)).
(* - simpl. move => _ h k e _. generalize e. rewrite e. clear e. move => e. by rewrite (eq_irrelevance e (refl_equal _)).*)
- simpl. move => n t0 IH0 t1 IH1 h k e s. rewrite <- IH0. rewrite <- IH1. move: s.
  generalize e. rewrite e. clear e. move => e. by rewrite (eq_irrelevance e (refl_equal _)).
- simpl. move => n t IH h k e s. rewrite map_map.
  specialize (IH (S h) (S k)). have e':h.+1 = k.+1 by auto. specialize (IH e').
  specialize (IH (TVar (ltn0Sn h) :: map (@tshiftL 0 1 _) s)). simpl in IH. rewrite map_map in IH.
  have ee:(TVar (n:=k.+1) (i:=0) (ltn0Sn k) :: map
                                               (fun x : Ty h =>
                                                tshiftL 0 1
                                                  (eq_rect h Ty x k e))
                                               s) = (eq_rect h.+1 Ty (TVar (n:=h.+1) (i:=0) (ltn0Sn h)) k.+1 e' :: 
          map
            (fun x : Ty h =>
             eq_rect h.+1 Ty (tshiftL 0 1 x) k.+1 e') s).
  f_equal ; clear IH ; first by (move: e' s ; rewrite -> e ; move => e' ; rewrite (eq_irrelevance e' (refl_equal _))).
  apply eq_map. clear. move: e'. generalize e. rewrite e. clear h e. move => e e'. rewrite (eq_irrelevance e (refl_equal _)).
  rewrite (eq_irrelevance e' (refl_equal _)). by [].
  rewrite ee. clear ee. rewrite <- IH. clear IH.
  move: e' s. generalize e. rewrite e. clear h e.
  move => e e'. rewrite (eq_irrelevance e' (refl_equal _)). by rewrite (eq_irrelevance e (refl_equal _)).
- simpl. move => n t IH h k e s. rewrite map_map.
  specialize (IH (S h) (S k)). have e':h.+1 = k.+1 by auto. specialize (IH e').
  specialize (IH (TVar (ltn0Sn h) :: map (@tshiftL 0 1 _) s)). simpl in IH. rewrite map_map in IH.
  have ee:(TVar (n:=k.+1) (i:=0) (ltn0Sn k) :: map
                                               (fun x : Ty h =>
                                                tshiftL 0 1
                                                  (eq_rect h Ty x k e))
                                               s) = (eq_rect h.+1 Ty (TVar (n:=h.+1) (i:=0) (ltn0Sn h)) k.+1 e' :: 
          map
            (fun x : Ty h =>
             eq_rect h.+1 Ty (tshiftL 0 1 x) k.+1 e') s).
  f_equal ; clear IH ; first by (move: e' s ; rewrite -> e ; move => e' ; rewrite (eq_irrelevance e' (refl_equal _))).
  apply eq_map. clear. move: e'. generalize e. rewrite e. clear h e. move => e e'. rewrite (eq_irrelevance e (refl_equal _)).
  rewrite (eq_irrelevance e' (refl_equal _)). by [].
  rewrite ee. clear ee. rewrite <- IH. clear IH.
  move: e' s. generalize e. rewrite e. clear h e.
  move => e e'. rewrite (eq_irrelevance e' (refl_equal _)). by rewrite (eq_irrelevance e (refl_equal _)).
- simpl. move => n t0 IH0 t1 IH1 h k e s. rewrite <- IH0. rewrite <- IH1. move: s.
  generalize e. rewrite e. clear e. move => e. by rewrite (eq_irrelevance e (refl_equal _)).
- simpl. move => n t IH h k e s. rewrite <- IH. move: s.
  generalize e. rewrite e. clear e. move => e. by rewrite (eq_irrelevance e (refl_equal _)).
Qed.

Lemma tsubst_shiftL' n (t:Ty n) k i m (s':seq (Ty (i+m))) (s:seq (Ty m)) :
    map (@tshiftL k i _) (take k s) = take k s' ->
    map (@tshiftL k i _) (drop k s) = drop (k+i) s' ->
    tsubst s' (tshiftL k i t) = tshiftL k i (tsubst s t).
move => n t k i m s' s m0 m1.
have r:=tsubst_shiftL t. specialize (r k i m). specialize (r (map (fun x => eq_rect _ Ty x _ (addnC i m)) s') s).
rewrite <- tsubst_eq in r. have r':=f_equal (fun x => eq_rect _ Ty x _ (addnC m i)) (r _ _). clear r.
rewrite (eq_nat_comp (addnC i m) (addnC m i) (tsubst s' (tshiftL k i t))) in r'.
rewrite (eq_irrelevance (trans_eq (addnC i m) (addnC m i)) (refl_equal _)) in r'.
simpl in r'. rewrite r' ; first by [].
- clear r'. rewrite <- map_take. rewrite <- m0. clear m0. rewrite map_map. apply eq_map. move => x.
  simpl. unfold tshiftL. rewrite eq_nat_comp. by rewrite (eq_irrelevance (trans_eq (addnC m i) (addnC i m)) (refl_equal _)).
- rewrite <- map_drop. rewrite <- m1. rewrite map_map. apply eq_map. move => x.
  simpl. unfold tshiftL. rewrite eq_nat_comp. by rewrite (eq_irrelevance (trans_eq (addnC m i) (addnC i m)) (refl_equal _)).
Qed.

Lemma tsubst_map i (t:Ty i) n (s:seq (Ty n)) m (s':seq (Ty m)) : tsubst s (tsubst s' t) = tsubst (map (@tsubst _ s _) s') t.
move => i t.
elim: i / t ; try by [] ; try (by move => i t0 IH0 n s m s' ; simpl; rewrite IH0) ;
              try (by move => i t0 IH0 t1 IH1 n s m s' ; simpl ; rewrite IH0 ; rewrite IH1).
- simpl. move => i j l n s m s'. case_eq (j < size s').
  + move => L. by rewrite -> (@nth_map _ (@Unit _) _ (@Unit _) (@tsubst _ s _)) ; last by [].
  + move => L. have a:=sym_eq (ltnNge j (size s')). rewrite L in a.
    have b:=negbT a. rewrite (nth_default _ (negbNE b)). rewrite <- (size_map (@tsubst _ s _) s') in b.
    by rewrite (nth_default _ (negbNE b)).
- move => i t IH n s m s'. simpl. rewrite map_map. rewrite IH. clear IH.
  f_equal. have e:forall a, map (fun x : Ty m => tsubst (TVar (ltn0Sn n) :: map (@tshiftL 0 1 _) s) (tshiftL 0 1 x)) a =
                  map (fun x : Ty m => tshiftL 0 1 (tsubst s x)) a.
    apply eq_map. move => a. simpl. clear.
    have r:=(@tsubst_shiftL' m a 0 1 _ _ s). rewrite drop0 in r. rewrite take0 in r. simpl in r.
    specialize (r (TVar (n:=n.+1) (i:=0) (ltn0Sn n) :: map (@tshiftL 0 1 _) s)).
    rewrite take0 in r. specialize (r (refl_equal _)). unfold addn in r. unfold addn_rec in r. simpl in r.
    rewrite drop0 in r. specialize (r (refl_equal _)). by rewrite <- r.
  rewrite <- e. clear e. simpl. by rewrite map_map.
- move => i t IH n s m s'. simpl. rewrite map_map. rewrite IH. clear IH.
  f_equal. have e:forall a, map (fun x : Ty m => tsubst (TVar (ltn0Sn n) :: map (@tshiftL 0 1 _) s) (tshiftL 0 1 x)) a =
                  map (fun x : Ty m => tshiftL 0 1 (tsubst s x)) a.
    apply eq_map. move => a. simpl. clear.
    have r:=(@tsubst_shiftL' m a 0 1 _ _ s). rewrite drop0 in r. rewrite take0 in r. simpl in r.
    specialize (r (TVar (n:=n.+1) (i:=0) (ltn0Sn n) :: map (@tshiftL 0 1 _) s)).
    rewrite take0 in r. specialize (r (refl_equal _)). unfold addn in r. unfold addn_rec in r. simpl in r.
    rewrite drop0 in r. specialize (r (refl_equal _)). by rewrite <- r.
  rewrite <- e. clear e. simpl. by rewrite map_map.
Qed.

Lemma tshiftR0 n (x:Ty n) k (a:n = n+0) : tshiftR k 0 x = eq_rect _ Ty x _ a.
move => n x. elim: n / x.
- move => n i l k a. simpl. case_eq (i < k) => ll.
  + have b:=(ssrnat.leq_trans l (leq_addr 0 n)). rewrite (eq_irrelevance (ssrnat.leq_trans l (leq_addr 0 n)) b). move: b.
    generalize a. rewrite <- a. clear a. move => a b. rewrite (eq_irrelevance a (refl_equal _)). simpl.
    by rewrite (eq_irrelevance b l).
  + have b:=(leq_add l (leqnn 0)). rewrite (eq_irrelevance (leq_add l (leqnn 0)) b). move: b. generalize a. rewrite <- a. clear a.
    move => a. rewrite (eq_irrelevance a (refl_equal _)). simpl. clear a.
    move => b. have c:i + 0 < n by apply b. rewrite (eq_irrelevance b c). clear b.
    move: c. rewrite addn0. move => c. by rewrite (eq_irrelevance c l).
- move => n k. simpl. rewrite addn0. move => a. by rewrite (eq_irrelevance a (refl_equal _)).
- move => n k. simpl. rewrite addn0. move => a. by rewrite (eq_irrelevance a (refl_equal _)).
- move => n t0 IH0 t1 IH1 k a. simpl. rewrite (IH0 _ a). rewrite (IH1 _ a). clear IH0 IH1 k.
  generalize a. rewrite <- a. clear a. move => a. by rewrite (eq_irrelevance a (refl_equal _)).
(* - move => n k. simpl. rewrite addn0. move => a. by rewrite (eq_irrelevance a (refl_equal _)).*)
- move => n t0 IH0 t1 IH1 k a. simpl. rewrite (IH0 _ a). rewrite (IH1 _ a). clear IH0 IH1 k.
  generalize a. rewrite <- a. clear a. move => a. by rewrite (eq_irrelevance a (refl_equal _)).
- move => n t IH k a. have a':n.+1 = (n + 0).+1 by auto. specialize (IH k.+1 a').
  simpl. rewrite IH. clear IH.
  have e:Mu (eq_rect n.+1 Ty t (n + 0).+1 a') = eq_rect n Ty (Mu t) (n + 0) a ; last by [].
  move: a'. generalize a. rewrite <- a. clear a. move => a a'. rewrite (eq_irrelevance a (refl_equal _)).
  by rewrite (eq_irrelevance a' (refl_equal _)).
- move => n t IH k a. have a':n.+1 = (n + 0).+1 by auto. specialize (IH k.+1 a').
  simpl. rewrite IH. clear IH.
  have e:All (eq_rect n.+1 Ty t (n + 0).+1 a') = eq_rect n Ty (All t) (n + 0) a ; last by [].
  move: a'. generalize a. rewrite <- a. clear a. move => a a'. rewrite (eq_irrelevance a (refl_equal _)).
  by rewrite (eq_irrelevance a' (refl_equal _)).
- move => n t0 IH0 t1 IH1 k a. simpl. rewrite (IH0 _ a). rewrite (IH1 _ a). clear IH0 IH1 k.
  generalize a. rewrite <- a. clear a. move => a. by rewrite (eq_irrelevance a (refl_equal _)).
- move => n t IH k a. simpl. rewrite (IH _ a). clear k IH.
  generalize a. rewrite <- a. clear a. move => a. by rewrite (eq_irrelevance a (refl_equal _)).
Qed.

Lemma tshiftL0 n (x:Ty n) k : tshiftL k 0 x = x.
move => n x k. unfold tshiftL. rewrite (tshiftR0 x k (addnC 0 n)).
rewrite eq_nat_comp. by rewrite (eq_irrelevance (trans_eq (addnC 0 n) (addnC n 0)) (refl_equal _)).
Qed.

(*** Typed terms  ***)

(* This is the untyped syntax *)

(*=ValueExp *)
Inductive Value (n:nat) : Set :=
| VAR: nat -> Value n
| LOC: nat -> Value n
| INT: nat -> Value n
| TLAM: Exp (S n) -> Value n
| LAM: Ty n -> Exp n -> Value n
(*| FIX: Ty n -> Ty n -> Exp n -> Value n*)
| UNIT : Value n
| P: Value n -> Value n -> Value n
| INL : Ty n -> Value n -> Value n
| INR : Ty n -> Value n -> Value n
| FOLD : Ty (S n) -> Value n -> Value n
(* | VOID: Ty n -> Value n -> Value n*)
with Exp (n:nat) : Set :=
| VAL: Value n -> Exp n
| FST: Value n -> Exp n
| SND: Value n -> Exp n
| OP: (nat -> nat -> nat) -> Value n -> Exp n
| UNFOLD: Value n -> Exp n
| REF: Value n -> Exp n
| BANG: Value n -> Exp n
| ASSIGN: Value n -> Value n -> Exp n
| LET: Exp n -> Exp n -> Exp n
| APP: Value n -> Value n -> Exp n
| TAPP: Value n -> Ty n -> Exp n
| CASE: Value n -> Exp n -> Exp n -> Exp n.
(*=End *)


(* begin hide *)
Scheme Value_rec2 := Induction for Value Sort Set
  with Exp_rec2 := Induction for Exp Sort Set.

Scheme Value_type2 := Induction for Value Sort Type
  with Exp_type2 := Induction for Exp Sort Type.

Scheme Value_ind2 := Induction for Value Sort Prop
  with Exp_ind2 := Induction for Exp Sort Prop.

Combined Scheme ExpValue_ind from Value_ind2, Exp_ind2.

Fixpoint free_varV n (v:Value n) (l:seq nat) : bool :=
match v with
| VAR j => j \in l
| LOC j => true
| INT j => true
| TLAM e => free_varE e l
| LAM t e => free_varE e (O :: map S l)
| UNIT => true
| P v0 v1 => (free_varV v0 l) && (free_varV v1 l)
| INL t v => free_varV v l
| INR t v => free_varV v l
| FOLD t v => free_varV v l
end
with free_varE n (e:Exp n) (l:seq nat) : bool :=
match e with
| VAL v => free_varV v l
| FST v => free_varV v l
| SND v => free_varV v l
| OP op v => free_varV v l
| UNFOLD v => free_varV v l
| REF v => free_varV v l
| BANG v => free_varV v l
| ASSIGN v0 v1 => (free_varV v0 l) && (free_varV v1 l)
| LET e0 e1 => (free_varE e0 l) && (free_varE e1 (O :: map S l))
| APP v0 v1 => (free_varV v0 l) && (free_varV v1 l)
| TAPP v t => free_varV v l
| CASE v e0 e1 => (free_varV v l) && (free_varE e0 (O :: map S l)) && (free_varE e1 (O :: map S l))
end.

Definition closedV n (v:Value n) := free_varV v nil.
Definition closedE n (e:Exp n) := free_varE e nil.

Record cexpression (n:nat) : Type := CExp {
  cexp :> Exp n;
  _ : closedE cexp
}.

Record cvalue (n:nat) : Type := CValue {
  cval :> Value n;
  _ : closedV cval
}.

Lemma cvalueP n (v:cvalue n) : closedV v.
move => n. by case.
Qed.

Lemma cexpP n (v:cexpression n) : closedE v.
move => n. by case.
Qed.

Lemma map_cvalP n (X:seq (cvalue n)) : all (fun x => free_varV x [::]) (map (@cval _) X).
move => n. elim ; first by [].
move => v s IH. simpl. rewrite IH. rewrite andbT. by apply (cvalueP v).
Qed.

Lemma CExp_eq n (a b:Exp n) (A:closedE a) (B:closedE b) : a = b -> CExp A = CExp B.
move => n a b A B e. move: A B. rewrite e. clear a e. move => A B. by rewrite (eq_irrelevance A B).
Qed.

Lemma CValue_eq n (a b:Value n) (A:closedV a) (B:closedV b) : a = b -> CValue A = CValue B.
move => n a b A B e. move: A B. rewrite e. clear a e. move => A B. by rewrite (eq_irrelevance A B).
Qed.

Implicit Arguments CExp [n].
Implicit Arguments CValue [n].

Canonical Structure cvalue_subType (n:nat) :=
  Eval hnf in [subType for (@cval n) by (@cvalue_rect n)].

Canonical Structure cexp_subType (n:nat) :=
  Eval hnf in [subType for (@cexp n) by (@cexpression_rect n)].

Canonical Structure cUNIT n := @CValue n (@UNIT n) (refl_equal _).
Canonical Structure cINT n j := @CValue n (@INT n j) (refl_equal _).
Canonical Structure cLOC n j := @CValue n (@LOC n j) (refl_equal _).
Canonical Structure cTLAM n (e:cexpression n.+1) := @CValue n (TLAM e) (cexpP e).

Lemma andbB (b0 b1:bool) : b0 -> b1 -> b0 && b1.
move => b0 b1 A B. rewrite A. by rewrite B.
Qed.

Canonical Structure cP n (v0 v1 : cvalue n) := @CValue n (P v0 v1) (andbB (cvalueP v0) (cvalueP v1)).
Canonical Structure cINL n t (v : cvalue n) := @CValue n (INL t v) (cvalueP v).
Canonical Structure cINR n t (v : cvalue n) := @CValue n (INR t v) (cvalueP v).
Canonical Structure cFOLD n t (v : cvalue n) := @CValue n (FOLD t v) (cvalueP v).
Canonical Structure cVAL n (v:cvalue n) := @CExp n (VAL v) (cvalueP v).
Canonical Structure cFST n (v:cvalue n) := @CExp n (FST v) (cvalueP v).
Canonical Structure cSND n (v:cvalue n) := @CExp n (SND v) (cvalueP v).
Canonical Structure cOP op n (v:cvalue n) := @CExp n (OP op v) (cvalueP v).
Canonical Structure cUNFOLD n (v:cvalue n) := @CExp n (UNFOLD v) (cvalueP v).
Canonical Structure cREF n (v:cvalue n) := @CExp n (REF v) (cvalueP v).
Canonical Structure cBANG n (v:cvalue n) := @CExp n (BANG v) (cvalueP v).
Canonical Structure cASSIGN n (v0 v1:cvalue n) := @CExp n (ASSIGN v0 v1) (andbB (cvalueP v0) (cvalueP v1)).
Canonical Structure cAPP n (v0 v1:cvalue n) := @CExp n (APP v0 v1) (andbB (cvalueP v0) (cvalueP v1)).
Canonical Structure cTAPP n t (v:cvalue n) := @CExp n (TAPP v t) (cvalueP v).

(* end hide *)


Implicit Arguments UNIT [n].
Implicit Arguments VAR [n].
Implicit Arguments INT [n].
Implicit Arguments LOC [n].

(* Now this is the typing judgement *)

Definition StoreType i := FinDom [compType of nat] (Ty i).

(* begin hide *)
Reserved Notation "n |- a | d '|v-' b ':::' c" (at level  75).
Reserved Notation "n |- a | d '|e-' b ':::' c" (at level  75).

(* end hide *)
(**  printing |e-  $\ensuremath{\vdash_e}$ *)
(**  printing |v-  $\ensuremath{\vdash_v}$ *)
(**  printing :::  $\ensuremath{:}$ *)

Definition post_compt (T : compType) (T' T0 : Type) (g : T' -> T0) (f : FinDom T T') := post_comp (fun x => Some (g x)) f.

Fixpoint tweakR m n (t:Ty n) : Ty (n + m) :=
match t with
| TVar i l => @TVar _ i (ssrnat.leq_trans l (leq_addr _ _)) 
| Int => Int
| Unit => Unit
| Product t t' => Product (tweakR m t) (tweakR m t')
(*| Void => Void*)
| Sum t t' => Sum (tweakR m t) (tweakR m t')
| Mu t => Mu (tweakR m t)
| All t => All (tweakR m t)
| Arrow t t' => Arrow (tweakR m t) (tweakR m t')
| Ref t => Ref (tweakR m t)
end.

Definition tweakL i n (x:Ty n) := eq_rect _ Ty (tweakR i x) (i+n) (addnC _ _).

Inductive VTyping (i:nat) (env:TypeEnv i) (se:StoreType i) (t:Ty i) : Value i -> Type :=
  | TvVAR: forall m , nth_error env m = Some t -> i |- env | se |v- (VAR m) ::: t
  | TvLOC: forall t' l, se l = Some t' -> t = Ref t' -> i |- env | se |v- LOC l ::: t
  | TvINT: forall n , t = Int -> i |- env | se |v- (INT n) ::: t
  | TvTLAM: forall e t', t = All t' -> i.+1 |- map (@tshiftL 0 1 i) env | post_compt (@tshiftL 0 1 i) se |e- e ::: t' -> i |- env | se |v- (TLAM e) ::: t
  | TvLAMBDA: forall a b body, t = a --> b -> i |- a :: env | se |e- body ::: b -> 
                       i |- env | se |v- (LAM a body) ::: t
(*  | TvFIX: forall body t' t'', t = t' --> t'' -> i |- t' :: (t' --> t'') :: env | se |e- body ::: t'' -> 
                                            i |- env | se |v- (FIX t' t'' body) ::: t*)
  | TvUNIT: t = Unit -> i |- env | se |v- UNIT ::: t
  | TvP: forall a b e1 e2, t = a ** b -> i |- env | se |v- e1 ::: a ->
                              i |- env | se |v-  e2 ::: b -> i |- env | se |v- (P e1 e2) ::: t
  | TvINL: forall a b e, i |- env | se |v- e ::: a -> t = Sum a b -> i |- env | se |v- (INL b e) ::: t
  | TvINR: forall a b e, i |- env | se |v- e ::: b -> t = Sum a b -> i |- env | se |v- (INR a e) ::: t
  | TvFOLD: forall a e, i |- env | se |v- e ::: tsubst (Mu a::idsub 0 i) a -> t = Mu a -> i |- env | se |v- FOLD a e ::: t
(*  | TvVOID: forall e, i |- env |v- e ::: Void -> i |- env |v- VOID t e ::: t*)
where "i |- env | se |v- exp ::: type" := ( @VTyping i env se type exp )
with ETyping (i:nat) (env:TypeEnv i) (se:StoreType i) (t:Ty i) : Exp i -> Type :=
  | TeVAL: forall v, i |- env | se |v- v ::: t -> i |- env | se |e- (VAL v) :::t
  | TeLET: forall e e' t', i |- env | se |e- e' ::: t' -> i |- t' :: env | se |e- e ::: t ->
                           i |- env | se |e- (LET e' e) ::: t
  | TvFST: forall b e, i |- env | se |v- e ::: (t ** b) -> i |- env | se |e- (FST e) ::: t
  | TvSND: forall a e, i |- env | se |v- e ::: (a ** t) -> i |- env | se |e- (SND e) ::: t
  | TvOP: forall op exp, t = Int -> i |- env | se |v- exp ::: Product Int Int -> i |- env | se |e- (OP op exp) ::: t
  | TvUNFOLD: forall a e, i |- env | se |v- e ::: Mu a -> t = tsubst (Mu a::idsub 0 i) a -> i |- env | se |e- UNFOLD e ::: t
  | TvREF: forall e a, i |- env | se |v- e ::: a -> t = Ref a -> i |- env | se |e- REF e ::: t
  | TvBANG: forall e, i |- env | se |v- e ::: Ref t -> i |- env | se |e- BANG e ::: t
  | TvASSIGN: forall l e a, i |- env | se |v- l ::: Ref a -> i |- env | se |v- e ::: a -> t = Unit -> i |- env | se |e- ASSIGN l e ::: t
  | TeAPP: forall a rator rand, i |- env | se |v- rator::: a --> t ->
                                      i |- env | se |v- rand ::: a ->
                                      i |- env | se |e- (APP rator rand) ::: t
  | TeTAPP: forall e b a, i |- env | se |v- e ::: All b -> t = tsubst (a::idsub 0 i) b -> i |- env | se |e- TAPP e a ::: t
  | TeCASE: forall v e e' a b, i |- env | se |v- v ::: Sum a b -> i |- a :: env | se |e- e ::: t -> i |- b :: env | se |e- e' ::: t ->
               i |- env | se |e- CASE v e e' ::: t
where "i |- env | se |e- exp ::: type" := ( @ETyping i env se type exp ).

(* begin hide *)
Hint Resolve TvINT TeAPP TeCASE TeLET TeVAL TvVAR TvTLAM TLAM TvOP TvINL TvINR TvP TvSND TvFST TvASSIGN TvBANG TvREF.

Scheme VTyping_rec2 := Induction for VTyping Sort Set
  with ETyping_rec2 := Induction for ETyping Sort Set.

Scheme VTyping_rect2 := Induction for VTyping Sort Type
  with ETyping_rect2 := Induction for ETyping Sort Type.

Scheme VTyping_ind2 := Induction for VTyping Sort Prop
  with ETyping_ind2 := Induction for ETyping Sort Prop.

Combined Scheme Typing_ind from VTyping_ind2, ETyping_ind2.
(* end hide *)

Definition Typing_rect (P0 : forall i env se t v, i |- env | se |v- v ::: t -> Type)
                       (P1 : forall i env se t e, i |- env | se |e- e ::: t -> Type)
                          A0 A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 i (env:TypeEnv i) se t :
                    (forall v (d : i |- env | se |v- v ::: t), P0 i env se t v d) *
                    (forall e (d : i |- env | se |e- e ::: t), P1 i env se t e d) :=
pair (@VTyping_rect2 P0 P1 A0 A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 i env se t)
     (@ETyping_rect2 P0 P1 A0 A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 i env se t).

Definition Typing_rec i (P0 : forall i env se t v, i |- env | se |v- v ::: t -> Set)
                        (P1 : forall i env se t e, i |- env | se |e- e ::: t -> Set)
                          A0 A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 env se t :
                    (forall v (d : i |- env | se |v- v ::: t), P0 i env se t v d) *
                    (forall e (d : i |- env | se |e- e ::: t), P1 i env se t e d) :=
pair (@VTyping_rec2 P0 P1 A0 A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 i env se t)
     (@ETyping_rec2 P0 P1 A0 A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 i env se t).

Fixpoint vtsubst n (s:seq (Ty n)) m (v:Value m) : Value n :=
match v with
| VAR x => VAR x
| LOC l => LOC l
| INT l => INT l
| TLAM e => TLAM (@etsubst (S n) (TVar (ltn0Sn n) :: map (@tshiftL 0 1 _) s) _ e)
| LAM t e => LAM (tsubst s t) (etsubst s e)
(*| FIX t t' e => FIX (tsubst s t) (tsubst s t') (etsubst s e)*)
| UNIT => UNIT
| P v v' => P (vtsubst s v) (vtsubst s v')
| INL t v => INL (tsubst s t) (vtsubst s v)
| INR t v => INR (tsubst s t) (vtsubst s v)
| FOLD t v => FOLD (tsubst (TVar (ltn0Sn _) :: (map (@tshiftL 0 1 _) s)) t) (vtsubst s v)
(*| VOID t v => VOID (tsubst s t) (vtsubst s v)*)
end
with etsubst n (s:seq (Ty n)) m (e:Exp m) : Exp n :=
match e with
| VAL v => VAL (vtsubst s v)
| LET e e' => LET (etsubst s e) (etsubst s e')
| FST v => FST (vtsubst s v)
| SND v => SND (vtsubst s v)
| OP op v => OP op (vtsubst s v)
| UNFOLD v => UNFOLD (vtsubst s v)
| REF v => REF (vtsubst s v)
| BANG v => BANG (vtsubst s v)
| ASSIGN v v' => ASSIGN (vtsubst s v) (vtsubst s v')
| APP v v' => APP (vtsubst s v) (vtsubst s v')
| TAPP v t => TAPP (vtsubst s v) (tsubst s t)
| CASE v e e' => CASE (vtsubst s v) (etsubst s e) (etsubst s e')
end.

Lemma tsubst_shiftRW i n (x:Ty n) k m (s:seq (Ty m)) s' :
   take k s = take k s' -> drop (k+i) s = drop k s' -> tsubst s (tshiftR k i x) = tsubst s' x.
move => i n x. elim: n / x.
- move => j v l k m s s' m0 m1. simpl.
  case_eq (v < k) ; move => ll.
  + simpl. have mm:=f_equal (fun x => nth Unit x v) m0.
    rewrite (nth_take _ ll) in mm. by rewrite (nth_take _ ll) in mm.
  + simpl. have mm:=f_equal (fun x => nth Unit x (v - k)) m1.
    do 2 rewrite nth_drop in mm. rewrite ltnNge in ll. have l0:=negbFE ll. rewrite (subnKC l0) in mm.
    rewrite <- mm. rewrite (addnC k). rewrite <- addnA. rewrite (subnKC l0). by rewrite addnC.
- by [].
- by [].
- move => n t0 IH0 t1 IH1 k m s s' m0 m1. simpl.
  rewrite (IH0 _ _ _ _ m0 m1). by rewrite (IH1 _ _ _ _ m0 m1).
(*- by [].*)
- move => n t0 IH0 t1 IH1 k m s s' m0 m1. simpl.
  rewrite (IH0 _ _ _ _ m0 m1). by rewrite (IH1 _ _ _ _ m0 m1).
- move => n t IH k m s s' m0 m1. simpl. specialize (IH (S k) (S m) (TVar (ltn0Sn m) :: map (@tshiftL 0 1 _) s)).
  specialize (IH (TVar (ltn0Sn m) :: map (@tshiftL 0 1 _) s')).
  rewrite IH ; first by [].
  + simpl. f_equal. do 2 rewrite <- map_take. by rewrite m0.
  + simpl. do 2 rewrite <- map_drop. by rewrite <- m1.
- move => n t IH k m s s' m0 m1. simpl. specialize (IH (S k) (S m) (TVar (ltn0Sn m) :: map (@tshiftL 0 1 _) s)).
  specialize (IH (TVar (ltn0Sn m) :: map (@tshiftL 0 1 _) s')).
  rewrite IH ; first by [].
  + simpl. f_equal. do 2 rewrite <- map_take. by rewrite m0.
  + simpl. do 2 rewrite <- map_drop. by rewrite <- m1.
- move => n t0 IH0 t1 IH1 k m s s' m0 m1. simpl.
  rewrite (IH0 _ _ _ _ m0 m1). by rewrite (IH1 _ _ _ _ m0 m1).
- move => n t IH k m s s' m0 m1. simpl. by rewrite (IH _ _ _ _ m0 m1).
Qed.

Lemma tsubst_shiftLW i n (x:Ty n) k m (s:seq (Ty m)) s' :
   take k s = take k s' -> drop (k+i) s = drop k s' -> tsubst s (tshiftL k i x) = tsubst s' x.
move => i n x k m s s' m0 m1.
unfold tshiftL. have a:= (addnC n i). rewrite (eq_irrelevance (addnC n i) a).
generalize a. rewrite <- a. clear a. move => a. rewrite (eq_irrelevance a (refl_equal _)). simpl.
by apply (tsubst_shiftRW _ m0 m1).
Qed.

Lemma nth_idsubr j i n k (ll:i < k) (l':i < n) (l:j <= n) (s:seq (Ty n)) : 
   (forall i (ll: i < k - j) (l':i+j < n), nth Unit s i = TVar (n:=n) (i:=i+j) l') -> nth (@Unit _) (idsubr  (j:=j) s l) i = TVar l'.
elim.
- simpl. move => i n k ll l' l s IH. specialize (IH i). rewrite addn0 in IH. rewrite subn0 in IH.
  specialize (IH ll l'). apply IH.
- move => j IH i n k ll l' l s X. simpl. apply (IH i n k ll). clear IH. case.
  + simpl. rewrite add0n. move => e l0. by rewrite (eq_irrelevance l l0).
  + simpl. move => x l0 l1. specialize (X x). have l3:1 < k - j by apply: (ssrnat.leq_trans _ l0).
    have l2:= (ltn_sub2r l3 l0). rewrite subn1 in l2. simpl in l2. rewrite subn_sub in l2. rewrite addnS in l2.
    rewrite addn0 in l2. specialize (X l2).
    rewrite addnS in X. specialize (X l1). by apply X.
Qed.

Lemma nth_idsub i n j (l:j < i) : nth Unit (idsub n i) j = TVar (ltn_addl _ l).
move => i n j l. unfold idsub. rewrite (nth_idsubr l (ltn_addl _ l)) ; first by [].
move => k l'. have F:False ; last by []. rewrite subnn in l'. by rewrite ltn0 in l'.
Qed.

Lemma idsubr_cat i n s s' (l:i <= n) : idsubr (s' ++ s) l = idsubr s' l ++ s.
elim ; first by [].
move => i IH n s s' l. simpl. specialize (IH n s (TVar (n:=n) (i:=i) l :: s') (ltnW l)).
simpl in IH. by rewrite IH.
Qed.

Lemma idsubr_weakR i n n' s (l:i <= n) (l':i <= n + (n' - n)) : idsubr (j:=i) (map (@tweakR (n' - n) _) s) l' = map (@tweakR (n' - n) _) (idsubr s l).
elim ; first by [].
move => i IH n n' s l l'. simpl. specialize (IH _ _ (TVar (n:=n) (i:=i) l :: s) (ltnW l) (ltnW l')).
simpl in IH. rewrite (eq_irrelevance (ssrnat.leq_trans l (leq_addr (n' - n) n)) l') in IH. by rewrite IH.
Qed.

Lemma idsubr_weakL i n n' s (l:i <= n) (l':i <= (n' - n) + n) :
   idsubr (j:=i) (map (@tweakL (n' - n) _) s) l' = map (@tweakL (n' - n) _) (idsubr s l).
move => i n n' s l l'. rewrite (idsubr_cat (map (@tweakL (n' - n) _) s) nil).
rewrite (idsubr_cat s nil). rewrite map_cat. f_equal.
unfold tweakL. have a:=(addnC n (n' - n)). rewrite (eq_irrelevance (addnC n (n' - n)) a).
move: l'. generalize a. rewrite <- a. clear a. move => a. rewrite (eq_irrelevance a (refl_equal _)). simpl. clear a.
move => l'. apply trans_eq with (y:=map (@tweakR (n' - n) _) (idsubr (j:=i) [::] l)) ; last by [].
by rewrite (idsubr_weakR nil l l').
Qed.

Lemma idsub_weakL i j n l : map (@tweakL j _) (idsub n i) = idsubr (j:=i) nil l.
move => i j n l. unfold idsub. 
have a:=@idsubr_weakL i (n+i) (j+(n+i)) nil (leq_addl n i).
have e:j = j + (n+i) - (n+i) by rewrite addnK. move: l. rewrite e. clear e. move => l. by rewrite (a l).
Qed.

Lemma idsub_weakR i j n l : map (@tweakR j _) (idsub n i) = idsubr (j:=i) nil l.
move => i j n l. unfold idsub. 
have a:=@idsubr_weakR i (n+i) (j+(n+i)) nil (leq_addl n i).
have e:j = j + (n+i) - (n+i) by rewrite addnK. move: l. rewrite e. clear e. move => l. by rewrite (a l).
Qed.

Lemma tweakL_var i n k (l:i < n) (l':i < k + n) : tweakL k (TVar l) = TVar l'.
move => i n k l l'. unfold tweakL. simpl.
have a:=(ssrnat.leq_trans l (leq_addr k n)). rewrite (eq_irrelevance (ssrnat.leq_trans l (leq_addr k n)) a).
have b:=(addnC n k). rewrite (eq_irrelevance (addnC n k) b). move: a. generalize b. rewrite b. clear.
move => b. rewrite (eq_irrelevance b (refl_equal _)). simpl. move => a. by rewrite (eq_irrelevance a l').
Qed.

Lemma tshiftL_var n k j i (l:j < n) (l':i+j < i + n) : k <= j -> tshiftL k i (TVar l) = TVar l'.
move => n k j i l l' L. unfold tshiftL. have a:=(addnC n i). rewrite (eq_irrelevance (addnC n i) a).
move: l'. generalize a. rewrite <- a. clear a. move => a. rewrite (eq_irrelevance a (refl_equal _)). simpl.
move => l'. rewrite ltnNge. rewrite L. simpl. move: l'. rewrite (addnC i j). move => l'.
by rewrite (eq_irrelevance (leq_add (m1:=j.+1) (m2:=i) (n1:=n) (n2:=i) l (leqnn i)) l').
Qed.

Lemma idsubr_shiftL1 i n (l:0 < S n) s l' ll : TVar l :: map (@tshiftL 0 1 _) (idsubr (j:=i) s l') =
                                         idsubr (j:=i.+1) (map (@tshiftL 0 1 _) s) ll.
elim.
- simpl. move => n l s _ ll. by rewrite (eq_irrelevance l ll).
- move => i IH n l s l' ll. simpl.
  simpl. specialize (IH n l (TVar (n:=n) (i:=i) l' :: s) (ltnW l') (ltnW ll)).
  rewrite IH. simpl. clear IH. have e:i.+1 = 1 + i by rewrite addSn ; rewrite add0n.
  f_equal. f_equal. f_equal. move: ll. rewrite e. clear e. move => ll.
  by rewrite (tshiftL_var l' ll (leq0n _)).
Qed.

Lemma TVar_eq_rect n n' (e:n = n') j l l' : eq_rect n Ty (TVar (n:=n) (i:=j) l) n' e = TVar (n:=n') (i:=j) l'.
move => n n' e. generalize e. rewrite e. clear. move => e. rewrite (eq_irrelevance e (refl_equal _)). simpl.
move => j l l'. by rewrite (eq_irrelevance l l').
Qed.

Lemma idsubr_eq_rect n n' (e:n = n') j s l l' :
   map (fun x => eq_rect _ Ty x _ e) (idsubr (j:=j) s l) = idsubr (j:=j) (map (fun x => eq_rect _ Ty x _ e) s) l'.
move => n n' e. elim ; first by [].
move => j IH s l l'. simpl. rewrite (idsubr_cat (TVar (n:=n) (i:=j) l:: s) nil). rewrite map_cat.
specialize (IH nil (ltnW l) (ltnW l')). rewrite IH. clear IH. simpl. rewrite (idsubr_cat (TVar l' :: _) nil).
by rewrite (TVar_eq_rect e l l').
Qed.

Lemma idsubr_shiftL j n i (l:j <= j + n) (l':i <= n) ll :
   idsubr (j:=j) (map (@tshiftL 0 j _) (idsubr (j:=i) nil l')) l = idsubr (j:=j+i) nil ll.
elim.
- simpl. move => n i _ l' ll.
  apply trans_eq with (y:=map id (idsubr nil l')) ; first by apply eq_map ; move => x ; apply (tshiftL0 x).
  rewrite map_id. move: ll. rewrite (add0n i). move => ll. by rewrite (eq_irrelevance l' ll).
- move => j IH n i l l' ll. simpl.
  have a:=@idsubr_shiftL1 i n (ltn0Sn _) nil l'. have l0:= ll. rewrite (leq_add2l (j.+1) i n) in l0.
  specialize (a l0).
  have b:=f_equal (map (@tshiftL 0 j _)) a. clear a. simpl in b. rewrite map_map in b.
  have a:=(tshiftL_var (ltn0Sn n) _ (leqnn 0)). specialize (a j).
  have l1: j + 0 < j + n.+1 by rewrite (ltn_add2l j 0 n.+1) ; apply ltn0Sn. specialize (a l1).
  have l2:j < j + n.+1 by clear a ; rewrite addn0 in l1.
  have e:TVar (i:=j + 0) l1 = TVar (i:=j) l2 by 
    clear a ; move: l1 l2 ; rewrite (addn0 j) ; move => l1 l2 ; rewrite (eq_irrelevance l1 l2).
  rewrite e in a. clear e l1. rewrite a in b. clear a.
  have e:j.+1 + n = j + (S n) by rewrite addSn ; rewrite addnS.
  have e':map (fun x : Ty n => tshiftL 0 j (tshiftL 0 1 x)) (idsubr (j:=i) [::] l') =
         (map (fun x => eq_rect _ Ty (tshiftL 0 (j.+1) x) _ e) (idsubr (j:=i) nil l')).
    apply eq_map. move => x. simpl. rewrite tshiftL_tshiftL.
    have a:=(sym_eq (addnA j 1 n)). rewrite (eq_irrelevance (sym_eq (addnA j 1 n)) a).
    have c:j+1 = S j by rewrite addnS ; rewrite addn0. move: a. rewrite -> c. move => a.
    by rewrite (eq_irrelevance a e).
  rewrite e' in b. clear e'. specialize (IH (S n) i).
  rewrite (idsubr_cat (TVar (n:=1 + n) l0 :: nil) nil) in b. rewrite map_cat in b. simpl in b.
  have c:=f_equal (fun x => idsubr (j:=j) x (leq_addr _ _)) b. clear b.
  specialize (IH (leq_addr _ _)).
  rewrite (idsubr_cat ([:: tshiftL 0 j (TVar (n:=1 + n) (i:=i) l0)])
                       (map (@tshiftL 0 j _) (idsubr (j:=i) [::] (ltnW (m:=i) (n:=1 + n) l0)))) in c.
  have l3:j + i <= j + n.+1 by rewrite (leq_add2l j i n.+1) ; apply (leqW l0).
  specialize (IH (ltnW (n:=1 + n) l0) l3). rewrite IH in c. clear IH.
  have b:=f_equal (map (fun x => eq_rect _ Ty x _ (sym_eq e))) c. clear c.
  rewrite map_cat in b. simpl in b.   
  have c:= (tshiftL_var (l0: i < 1 + n) _). specialize (c 0 j).
  have l4:j + i < j + (1 + n) by rewrite (ltn_add2l j i (1+n)). specialize (c l4 (leq0n _)).
  have d:=f_equal (fun x => eq_rect _ Ty x _ (sym_eq e)) c.
  have f:eq_rect _ Ty (tshiftL 0 j (TVar (n:=1 + n) (i:=i) l0)) _ (sym_eq e) = TVar ll.
  rewrite d. clear. fold plus. move: ll. generalize e. rewrite e. clear. move => e.
  rewrite (eq_irrelevance e (refl_equal _)). simpl. move => ll. by rewrite (eq_irrelevance  l4 ll).
  rewrite f in b. clear f d c.
  rewrite (idsubr_eq_rect (sym_eq e) _ l3 (ltnW ll)) in b. rewrite (idsubr_cat [:: TVar ll] nil).
  fold plus in b. fold plus. fold addn_rec. fold addn_rec in b. fold addn. fold addn in b. simpl in b.
  rewrite <- b. clear b. clear. rewrite (idsubr_eq_rect (sym_eq e) _ (leq_addr n.+1 j) (ltnW (m:=j) (n:=j.+1 + n) l)).
  simpl. rewrite map_map. rewrite (TVar_eq_rect (sym_eq e) l2 l).
  f_equal. f_equal. apply eq_map. move => x. simpl. rewrite eq_nat_comp.
  by rewrite (eq_irrelevance (trans_eq e (sym_eq e)) (refl_equal _)).
Qed.

Lemma idsub_cat n i j a b :
   map (fun x => eq_rect _ Ty x _ b) (idsub (n+j) i) ++ 
      map (fun x => eq_rect _ Ty (tshiftL 0 i x) _ a) (idsub n j) = idsub n (i + j).
move => n i j a b. unfold idsub.
have c:=@idsubr_shiftL i (n+j) j (leq_addr _ _) (leq_addl _ _).
have l0:i + j <= i + (n + j) by rewrite (addnC n j) ; rewrite addnA ; apply leq_addr.
specialize (c l0).
have d:(i + (n + j)) = n + (i+j) by rewrite addnC ; rewrite (addnC i j) ; rewrite addnA.
have f:=f_equal (map (fun x => eq_rect _ Ty x _ d)) c.
rewrite (idsubr_eq_rect d _ l0 (leq_addl n (i + j))) in f. simpl in f. rewrite <- f. clear f c.
rewrite (idsubr_cat (map _ _) nil). rewrite map_cat. rewrite map_map.
f_equal ; last by rewrite (eq_irrelevance a d). move: d. generalize b.
rewrite <- b. clear b. move => b. rewrite (eq_irrelevance b (refl_equal _)). simpl. move => c. clear.
rewrite map_id.
by rewrite (idsubr_eq_rect c _ (leq_addr (n + j) i) (leq_addl (n + j) i)).
Qed.

Lemma tshiftL_int n i k : tshiftL k i (@Int n) = Int.
move => n i k. unfold tshiftL. have a:=(addnC n i). rewrite (eq_irrelevance (addnC n i) a). generalize a. rewrite <- a.
move => a'. by rewrite (eq_irrelevance a' (refl_equal _)).
Qed.

Lemma tshiftL_unit n i k : tshiftL k i (@Unit n) = Unit.
move => n i k. unfold tshiftL. have a:=(addnC n i). rewrite (eq_irrelevance (addnC n i) a). generalize a. rewrite <- a.
move => a'. by rewrite (eq_irrelevance a' (refl_equal _)).
Qed.

(*
Lemma tshiftL_void n i k : tshiftL k i (@Void n) = Void.
move => n i k. unfold tshiftL. have a:=(addnC n i). rewrite (eq_irrelevance (addnC n i) a). generalize a. rewrite <- a.
move => a'. by rewrite (eq_irrelevance a' (refl_equal _)).
Qed.*)

Lemma tshiftL_pair i k n (t0 t1:Ty n) : tshiftL k i (t0 ** t1) = tshiftL k i t0 ** tshiftL k i t1.
move => i k n t0 t1. unfold tshiftL. have a:=(addnC n i). rewrite (eq_irrelevance (addnC n i) a). generalize a. rewrite <- a.
move => a'. by rewrite (eq_irrelevance a' (refl_equal _)).
Qed.

Lemma tshiftL_sum i k n (t0 t1:Ty n) : tshiftL k i (Sum t0 t1) = Sum (tshiftL k i t0) (tshiftL k i t1).
move => i k n t0 t1. unfold tshiftL. have a:=(addnC n i). rewrite (eq_irrelevance (addnC n i) a). generalize a. rewrite <- a.
move => a'. by rewrite (eq_irrelevance a' (refl_equal _)).
Qed.

Lemma tshiftL_var2 n k j i (l : j < n) (l' : j < i + n) : j < k -> tshiftL k i (TVar l) = TVar l'.
move => n k j i l l' e. unfold tshiftL. have a:=(addnC n i). rewrite (eq_irrelevance (addnC n i) a).
simpl. rewrite e. have ll:=(ssrnat.leq_trans l (leq_addr i n)). rewrite (eq_irrelevance (ssrnat.leq_trans l (leq_addr i n)) ll).
move: ll. generalize a. rewrite -> a. clear.  move => a. rewrite (eq_irrelevance a (refl_equal _)). simpl.
move => ll. by rewrite (eq_irrelevance ll l').
Qed.

Lemma tshiftL_mu i k n (e: i + n.+1 = (i+n).+1) (t:Ty n.+1) : tshiftL k i (Mu t) = Mu (eq_rect _ Ty (tshiftL k.+1 i t) _ e).
move => i k n e t. unfold tshiftL.
have a:=(addnC n i). rewrite (eq_irrelevance (addnC n i) a). move: e. generalize a. rewrite <- a. clear a.
move => a e. rewrite (eq_irrelevance a (refl_equal _)). simpl.
rewrite (eq_nat_comp). have e':=(trans_eq (addnC n.+1 i) e). rewrite (eq_irrelevance (trans_eq (addnC n.+1 i) e) e').
by rewrite (eq_irrelevance e' (refl_equal _)).
Qed.

Lemma tshiftL_all i k n (e: i + n.+1 = (i+n).+1) (t:Ty n.+1) : tshiftL k i (All t) = All (eq_rect _ Ty (tshiftL k.+1 i t) _ e).
move => i k n e t. unfold tshiftL.
have a:=(addnC n i). rewrite (eq_irrelevance (addnC n i) a). move: e. generalize a. rewrite <- a. clear a.
move => a e. rewrite (eq_irrelevance a (refl_equal _)). simpl.
rewrite (eq_nat_comp). have e':=(trans_eq (addnC n.+1 i) e). rewrite (eq_irrelevance (trans_eq (addnC n.+1 i) e) e').
by rewrite (eq_irrelevance e' (refl_equal _)).
Qed.

Lemma tshiftL_arrow i k n (t0 t1:Ty n) : tshiftL k i (t0 --> t1) = tshiftL k i t0 --> tshiftL k i t1.
move => i k n t0 t1. unfold tshiftL. have a:=(addnC n i). rewrite (eq_irrelevance (addnC n i) a). generalize a. rewrite <- a.
move => a'. by rewrite (eq_irrelevance a' (refl_equal _)).
Qed.

Lemma tshiftL_ref i k n (t:Ty n) : tshiftL k i (Ref t) = Ref (tshiftL k i t).
move => i k n t. unfold tshiftL. have a:=(addnC n i). rewrite (eq_irrelevance (addnC n i) a). generalize a. rewrite <- a.
move => a'. by rewrite (eq_irrelevance a' (refl_equal _)).
Qed.

Lemma size_idsubr n i s (l:i <= n) : size (idsubr s l) = i + size s.
move => n. elim ; first by [].
move => i IH s l. simpl. rewrite (IH (TVar l :: s) (ltnW l)). simpl. by rewrite addnS.
Qed.

Lemma size_idsub n i : size (idsub n i) = i.
move => n i. unfold idsub. by rewrite size_idsubr.
Qed.

Lemma nth_idsubr2 j i n (l:j <= n) (s:seq (Ty n)) : j <= i ->
      nth Unit (idsubr (j:=j) s l) i = nth Unit s (i-j).
move => j i n l s ll. rewrite (idsubr_cat s nil). rewrite nth_cat. rewrite size_idsubr. simpl. rewrite addn0.
rewrite ltnNge. by rewrite ll.
Qed.

Lemma nth_idsubr3 j i n (l:j <= n) (s:seq (Ty n)) : nth Unit (idsubr (j:=j) s l) i = Unit ->
    (forall i, nth_error s i <> Some Unit) -> j + size s <= i.
elim.
- move => i n l s E E'. rewrite add0n. simpl in E. specialize (E' i). clear l.
  elim: s i E E' ; first by intros ; apply leq0n.
  move => t s IH. case.
  + simpl. move => e. by rewrite e.
  + simpl. move => i E E'. specialize (IH i E E'). by apply IH.
- move => j IH i n l s E E'. simpl in E. have a:=IH _ _ _ _ E. simpl @size in a.
  rewrite addnS in a. apply a. case ; first by []. simpl. move => k. by apply E'.
Qed.

Lemma nth_idsub3 j i n : nth Unit (idsub n j) i = Unit -> j <= i.
move => j i n L. unfold idsub in L. have a:= (nth_idsubr3 L). simpl in a. by rewrite addn0 in a ; apply a.
Qed.

Lemma nth_nondefault T (x:T) s i : nth x s i <> x -> i < size s.
move => T x. elim. move => i. by rewrite nth_default.
- move => t s IH. case. move => _. simpl. by apply ltn0Sn.
  move => i. simpl. move => X. by apply (IH _ X).
Qed.

Lemma tsubst_idsub i n (x:Ty n) k (s:seq (Ty (n + i))) :
   (forall j, j < k -> nth Unit s j = nth Unit (idsub 0 (n+i)) j) ->
   (forall j, k <= j -> nth Unit s j = nth Unit (idsub 0 (n+i)) (i+j)) -> tsubst s x = tshiftR k i x.
move => i n x. elim: n / x.
- move => n j l k s L L'. simpl. case_eq (j < k) => E.
  + specialize (L _ E). rewrite L. rewrite (nth_idsub _ (ltn_addr i l)).
    by rewrite (eq_irrelevance (ltn_addl 0 (ltn_addr i l)) (ssrnat.leq_trans l (leq_addr i n))).
  + rewrite ltnNge in E. have E':=negbFE E. specialize (L' _ E'). rewrite L'.
    have l':=l. rewrite <- (ltn_add2r i) in l'. rewrite (addnC i j).
    rewrite (nth_idsub _ l'). by rewrite (eq_irrelevance (ltn_addl 0 l') (leq_add l (leqnn i))).
- by [].
- by [].
- move => n t0 IH0 t1 IH1 k s L L'. simpl. rewrite (IH0 k s L L'). by rewrite (IH1 k s L L').
(*- by [].*)
- move => n t0 IH0 t1 IH1 k s L L'. simpl. rewrite (IH0 k s L L'). by rewrite (IH1 k s L L').
- simpl. move => n t IH k s L L'. specialize (IH k.+1 (TVar (n:=(n + i).+1) (i:=0) (ltn0Sn (n + i)) :: map (@tshiftL 0 1 _) s)).
  rewrite <- IH ; first by [].
  + case ; first by move => _ ; rewrite (nth_idsub 0 (ltn0Sn (n + i))) ;
      rewrite <- (eq_irrelevance (ltn0Sn (n + i)) (ltn_addl 0 (ltn0Sn (n + i)))).
    move => j l. specialize (L j l). rewrite {2}[nth] lock. simpl. unlock. case_eq (j < size s) => E.
    * rewrite (nth_map Unit _ _ E). rewrite L. clear. case_eq (j < n+i) => E.
      - rewrite (nth_idsub 0 E). have b:=E. rewrite <- (ltn_add2l 1) in b. do 2 rewrite addSn in b.
        do 2 rewrite add0n in b. have a:= (nth_idsub 0 b). unfold addn in a. unfold addn_rec in a. simpl in a.
        unfold addn. unfold addn_rec. simpl. rewrite a. clear.
        by rewrite (@tshiftL_var (n+i) 0 j 1 (ltn_addl 0 E) (ltn_addl 0 b) (leq0n _)).
      - rewrite ltnNge in E. have E':=negbFE E. rewrite (nth_default Unit) ; last by rewrite size_idsub.
        rewrite (nth_default Unit) ; last by rewrite (size_idsub 0 (n.+1+i)) ; apply E'.
        by rewrite tshiftL_unit.
    * rewrite ltnNge in E. have E':=negbFE E. rewrite (nth_default Unit) ; last by rewrite size_map.
      rewrite (nth_default Unit E') in L. have a:=@nth_idsub3 (n+i) j 0 (sym_eq L).
      by rewrite (nth_default Unit) ; last by rewrite (size_idsub 0 (n.+1+i)) ; apply a.
  + case ; first by []. simpl.
  + move => j l. specialize (L' j l). case_eq (j < size s) => E.
    * rewrite (nth_map Unit _ _ E). rewrite L'. clear. rewrite (addnC i j).
      case_eq ((j + i) < (n + i)) => l. rewrite (nth_idsub _ l).
      have e:= (tshiftL_var (ltn_addl 0 l)). specialize (e 0 1).
      have ll:1 + (j + i) < 1 + (0 + (n + i)) by rewrite add0n ; do 2 rewrite addSn ; do 2 rewrite add0n ; apply l.
      specialize (e ll (leq0n _)). rewrite e. clear e.
      have l': (i + j.+1) < (n.+1 + i) by rewrite addnS ; rewrite addnC ; rewrite addSn ; apply l.
      rewrite (nth_idsub _ l'). clear. move: ll l'. unfold addn. unfold addn_rec. simpl. fold addn_rec.  fold addn.
      rewrite addnS. rewrite (addnC i j). move => l ll. by rewrite (eq_irrelevance l (ltn_addl 0 ll)).
    * rewrite ltnNge in l. have ll:=negbFE l. clear l. have l:=ll. rewrite <- (leq_add2l 1) in l.
      do 2 rewrite addSn in l. do 2 rewrite add0n in l. rewrite (nth_default Unit) ; last by rewrite size_idsub.
      rewrite (nth_default Unit) ; last by rewrite size_idsub ; rewrite addnS ; rewrite (addnC i j) ; apply l.
      by rewrite tshiftL_unit.
  + rewrite ltnNge in E. have E':=negbFE E. clear E. rewrite (nth_default Unit) ; last by rewrite size_map.
    rewrite (nth_default Unit E') in L'.  have a:=@nth_idsub3 (n+i) _ 0 (sym_eq L').
    by rewrite (nth_default Unit) ; last (rewrite size_idsub ; rewrite addnS).
- simpl. move => n t IH k s L L'. specialize (IH k.+1 (TVar (n:=(n + i).+1) (i:=0) (ltn0Sn (n + i)) :: map (@tshiftL 0 1 _) s)).
  rewrite <- IH ; first by [].
  + case ; first by move => _ ; rewrite (nth_idsub 0 (ltn0Sn (n + i))) ;
      rewrite <- (eq_irrelevance (ltn0Sn (n + i)) (ltn_addl 0 (ltn0Sn (n + i)))).
    move => j l. specialize (L j l). rewrite {2}[nth] lock. simpl. unlock. case_eq (j < size s) => E.
    * rewrite (nth_map Unit _ _ E). rewrite L. clear. case_eq (j < n+i) => E.
      - rewrite (nth_idsub 0 E). have b:=E. rewrite <- (ltn_add2l 1) in b. do 2 rewrite addSn in b.
        do 2 rewrite add0n in b. have a:= (nth_idsub 0 b). unfold addn in a. unfold addn_rec in a. simpl in a.
        unfold addn. unfold addn_rec. simpl. rewrite a. clear.
        by rewrite (@tshiftL_var (n+i) 0 j 1 (ltn_addl 0 E) (ltn_addl 0 b) (leq0n _)).
      - rewrite ltnNge in E. have E':=negbFE E. rewrite (nth_default Unit) ; last by rewrite size_idsub.
        rewrite (nth_default Unit) ; last by rewrite (size_idsub 0 (n.+1+i)) ; apply E'.
        by rewrite tshiftL_unit.
    * rewrite ltnNge in E. have E':=negbFE E. rewrite (nth_default Unit) ; last by rewrite size_map.
      rewrite (nth_default Unit E') in L. have a:=@nth_idsub3 (n+i) j 0 (sym_eq L).
      by rewrite (nth_default Unit) ; last by rewrite (size_idsub 0 (n.+1+i)) ; apply a.
  + case ; first by []. simpl.
  + move => j l. specialize (L' j l). case_eq (j < size s) => E.
    * rewrite (nth_map Unit _ _ E). rewrite L'. clear. rewrite (addnC i j).
      case_eq ((j + i) < (n + i)) => l. rewrite (nth_idsub _ l).
      have e:= (tshiftL_var (ltn_addl 0 l)). specialize (e 0 1).
      have ll:1 + (j + i) < 1 + (0 + (n + i)) by rewrite add0n ; do 2 rewrite addSn ; do 2 rewrite add0n ; apply l.
      specialize (e ll (leq0n _)). rewrite e. clear e.
      have l': (i + j.+1) < (n.+1 + i) by rewrite addnS ; rewrite addnC ; rewrite addSn ; apply l.
      rewrite (nth_idsub _ l'). clear. move: ll l'. unfold addn. unfold addn_rec. simpl. fold addn_rec.  fold addn.
      rewrite addnS. rewrite (addnC i j). move => l ll. by rewrite (eq_irrelevance l (ltn_addl 0 ll)).
    * rewrite ltnNge in l. have ll:=negbFE l. clear l. have l:=ll. rewrite <- (leq_add2l 1) in l.
      do 2 rewrite addSn in l. do 2 rewrite add0n in l. rewrite (nth_default Unit) ; last by rewrite size_idsub.
      rewrite (nth_default Unit) ; last by rewrite size_idsub ; rewrite addnS ; rewrite (addnC i j) ; apply l.
      by rewrite tshiftL_unit.
  + rewrite ltnNge in E. have E':=negbFE E. clear E. rewrite (nth_default Unit) ; last by rewrite size_map.
    rewrite (nth_default Unit E') in L'.  have a:=@nth_idsub3 (n+i) _ 0 (sym_eq L').
    by rewrite (nth_default Unit) ; last (rewrite size_idsub ; rewrite addnS).
- move => n t0 IH0 t1 IH1 k s L L'. simpl. rewrite (IH0 k s L L'). by rewrite (IH1 k s L L').
- move => n t0 IH0 k s L L'. simpl. by rewrite (IH0 k s L L').
Qed.

Lemma seq_ext T (s s':seq T) : (forall i, nth_error s i = nth_error s' i) -> s = s'.
move => T. elim.
- case ; first by []. move => t s E. by specialize (E 0).
- move => t e IH. case ; first by move => E ; specialize (E 0).
  move => t' s' X. have e':= (X 0). simpl in e'. case: e'. move => e'. rewrite e'. clear e'.
  specialize (IH s'). have X':=fun i => (X (S i)). simpl in X'. clear X. by rewrite (IH X').
Qed.

Lemma tsubst_idsubL i n (x:Ty n) k (s:seq (Ty (i + n))) :
   (forall j, j < k -> nth Unit s j = nth Unit (idsub 0 (i+n)) j) ->
   (forall j, k <= j -> nth Unit s j = nth Unit (idsub 0 (i+n)) (i+j)) -> tsubst s x = tshiftL k i x.
unfold tshiftL. move => i n. have a:=(addnC n i). rewrite (eq_irrelevance (addnC n i) a).
generalize a. rewrite <- a. clear a. move => a. rewrite (eq_irrelevance a (refl_equal _)). simpl. clear a.
move => x k s E E'. by apply (tsubst_idsub _ E E').
Qed.

Lemma tsubst_id n (x:Ty n) : tsubst (idsub 0 n) x = x.
move => n x. unfold idsub.
by rewrite (@tsubst_idsubL 0 n x 0 (idsubr (j:=n) [::] (leq_addl 0 n))) ; first by rewrite (tshiftL0 x).
Qed.

Lemma minSS i j : minn i.+1 j.+1 = (minn i j).+1.
move => i j. unfold minn. case_eq (i.+1 < j.+1) => X. have Y:i < j by apply X. by rewrite Y.
have Y:i < j = false by apply X. by rewrite Y.
Qed.

Lemma take_take T (l:seq T) i j : take i (take j l) = take (minn i j) l.
move => T. elim ; first by [].
move => e l IH. case.
- simpl. move => j ; rewrite (min0n j) ; case: j ; first by rewrite take0.
  move => j. by rewrite take0.
- move => i. case ; first by [].
  move => j. simpl. rewrite minSS. by rewrite IH.
Qed.

Lemma drop_take T i (l:seq T) j : i < j -> drop i (take j l) = take (j - i) (drop i l).
move => T. elim.
- move => l j _. do 2 rewrite drop0. by rewrite subn0.
- move => i IH s. case ; first by rewrite ltn0.
  move => j l. case: s ; first by [].
  move => e s. specialize (IH s j l). simpl. rewrite IH. by rewrite subSS.
Qed.

Lemma tsubst_map_idr n m i s (l:i <= m) : i <= size s -> map (@tsubst n s _) (idsubr (j:=i) nil l) = take i s.
move => n m. elim.
- simpl. move => s _ e. by rewrite take0.
- move => i IH s l e. simpl. rewrite (idsubr_cat _ nil). rewrite map_cat. simpl.
  specialize (IH s (ltnW l) (leqW e)). rewrite IH. clear IH. rewrite <- (cat_take_drop i).
  rewrite take_take. unfold minn. rewrite (ltnSn). f_equal.
  rewrite (drop_take _ (ltnSn i)).
  rewrite subSnn. have a:= nth_take Unit (ltn0Sn 0) (drop i s). rewrite (nth_drop) in a. rewrite addn0 in a.
  rewrite <- a. clear a. clear l m. elim: i s e.
  + simpl. move => s. rewrite drop0. case: s ; first by rewrite ltn0.
    move => e s _. simpl. by rewrite take0.
  + move => i IH. case ; first by rewrite ltn0.
    move => e s. simpl @drop. move => l. by rewrite <- IH.
Qed.

Lemma tsubst_map_id i n (s:seq (Ty n)) : i <= size s -> map (@tsubst _ s _) (idsub n i) = take i s.
move => i n s L. unfold idsub. by rewrite tsubst_map_idr.
Qed.

Lemma tsubst_ext n (x:Ty n) m (s s':seq (Ty m)) :
   (forall i, i < n -> nth Unit s i = nth Unit s' i) -> tsubst s x = tsubst s' x.
move => n x. elim: n / x ; try by [].
- move => n i l m s s' X. simpl. by apply (X _ l).
- move => n t0 IH0 t1 IH1 m s s' X. simpl. rewrite (IH0 _ _ _ X). by rewrite (IH1 _ _ _ X).
- move => n t0 IH0 t1 IH1 m s s' X. simpl. rewrite (IH0 _ _ _ X). by rewrite (IH1 _ _ _ X).
- move => n t IH m s s' X. simpl.
  specialize (IH (S m) (TVar (ltn0Sn m) :: map (@tshiftL 0 1 _) s) (TVar (ltn0Sn m) :: map (@tshiftL 0 1 _) s')).
  rewrite IH ; first by []. case; first by []. move => i L. simpl. specialize (X _ L).
  case_eq (i < size s).
  + case_eq (i < size s').
    * move => Y Z. rewrite (nth_map Unit) ; last by [].
      rewrite (nth_map Unit) ; last by []. by rewrite X.
    * move => Y Z. rewrite ltnNge in Y. have YY:=negbFE Y.
      rewrite (@nth_default _ _ (map _ s')) ; last by rewrite size_map. rewrite (nth_default _ YY) in X.
      rewrite (nth_map Unit _ _ Z). rewrite X. unfold tshiftL. have a:=(addnC m 1). rewrite (eq_irrelevance (addnC m 1) a).
      generalize a. simpl. rewrite a. clear a. move => a. by rewrite (eq_irrelevance a (refl_equal _)).
  + case_eq (i < size s').
    * move => Z Y. rewrite ltnNge in Y. have YY:=negbFE Y.
      rewrite (@nth_default _ _ (map _ s)) ; last by rewrite size_map. rewrite (nth_default _ YY) in X.
      rewrite (nth_map Unit _ _ Z). rewrite <- X. unfold tshiftL. have a:=(addnC m 1). rewrite (eq_irrelevance (addnC m 1) a).
      generalize a. simpl. rewrite a. clear a. move => a. by rewrite (eq_irrelevance a (refl_equal _)).
    * move => Y Z. rewrite ltnNge in Y. have YY:=negbFE Y. rewrite ltnNge in Z. have ZZ:=negbFE Z.
      rewrite (nth_default Unit ZZ) in X. rewrite (nth_default Unit YY) in X.
      rewrite (nth_default Unit) ; last by rewrite size_map.
      rewrite (nth_default Unit) ; last by rewrite size_map.
      by [].
- move => n t IH m s s' X. simpl.
  specialize (IH (S m) (TVar (ltn0Sn m) :: map (@tshiftL 0 1 _) s) (TVar (ltn0Sn m) :: map (@tshiftL 0 1 _) s')).
  rewrite IH ; first by []. case; first by []. move => i L. simpl. specialize (X _ L).
  case_eq (i < size s).
  + case_eq (i < size s').
    * move => Y Z. rewrite (nth_map Unit) ; last by [].
      rewrite (nth_map Unit) ; last by []. by rewrite X.
    * move => Y Z. rewrite ltnNge in Y. have YY:=negbFE Y.
      rewrite (@nth_default _ _ (map _ s')) ; last by rewrite size_map. rewrite (nth_default _ YY) in X.
      rewrite (nth_map Unit _ _ Z). rewrite X. unfold tshiftL. have a:=(addnC m 1). rewrite (eq_irrelevance (addnC m 1) a).
      generalize a. simpl. rewrite a. clear a. move => a. by rewrite (eq_irrelevance a (refl_equal _)).
  + case_eq (i < size s').
    * move => Z Y. rewrite ltnNge in Y. have YY:=negbFE Y.
      rewrite (@nth_default _ _ (map _ s)) ; last by rewrite size_map. rewrite (nth_default _ YY) in X.
      rewrite (nth_map Unit _ _ Z). rewrite <- X. unfold tshiftL. have a:=(addnC m 1). rewrite (eq_irrelevance (addnC m 1) a).
      generalize a. simpl. rewrite a. clear a. move => a. by rewrite (eq_irrelevance a (refl_equal _)).
    * move => Y Z. rewrite ltnNge in Y. have YY:=negbFE Y. rewrite ltnNge in Z. have ZZ:=negbFE Z.
      rewrite (nth_default Unit ZZ) in X. rewrite (nth_default Unit YY) in X.
      rewrite (nth_default Unit) ; last by rewrite size_map.
      rewrite (nth_default Unit) ; last by rewrite size_map.
      by [].
- move => n t0 IH0 t1 IH1 m s s' X. simpl. rewrite (IH0 _ _ _ X). by rewrite (IH1 _ _ _ X).
- move => n t IH m s s' X. simpl. by rewrite (IH _ _ _ X).
Qed.

Lemma tsubst_Veq i E S v t : i |- E | S |v- v ::: t -> forall E', E = E' -> forall S', S = S' -> i |- E' | S' |v- v ::: t.
move => i E S v t D E' e S' e'. rewrite <- e. rewrite <- e'. by apply D.
Qed.

Lemma tsubst_Eeq i E S v t : i |- E | S |e- v ::: t -> forall E', E = E' -> forall S', S = S' -> i |- E' | S' |e- v ::: t.
move => i E S v t D E' e S' e'. rewrite <- e. rewrite <- e'. by apply D.
Qed.

Lemma findom_ext T T' (f g : FinDom T T') : findom_t f = findom_t g -> f = g.
move => T T'. case =>l X. case => l' X'. simpl. move => e. move: X X'. rewrite e. clear l e.
move => X X'. by rewrite (eq_irrelevance X X').
Qed.

Lemma post_comp_comp T T' T'' (f:T' -> option T'') (g:T -> option T') X (x:FinDom X T) :
   post_comp f (post_comp g x) = post_comp (fun x => option_bind f (g x)) x.
move => T T' T'' f g X x. apply findom_ext. simpl. case: x. simpl. move => l _. elim: l ; first by [].
case => e0 e1 s IH. simpl. case_eq (g e1) ; last by simpl ; rewrite IH.
move => t E. simpl. case_eq (f t) ; last by simpl ; rewrite IH. simpl.
move => t' E'. by rewrite IH.
Qed.

Lemma post_comp_eq T T' T'' (f g:T' -> option T'') : f =1 g -> @post_comp T _ _ f =1 post_comp g.
move => T T' T'' f g E x. apply findom_ext. simpl. case: x. simpl. move => s _. elim: s ; first by [].
move => t s IH. simpl. rewrite (E t.2). by case (g t.2) ; simpl ; rewrite IH.
Qed.

Lemma tsubst_deriv i E S t :
   (forall v, i |- E | S |v- v ::: t -> forall m (s:seq (Ty m)), i <= size s -> m |- map (@tsubst _ s _) E | post_compt (@tsubst _ s _) S |v- vtsubst s v ::: tsubst s t) *
   (forall e, i |- E | S |e- e ::: t -> forall m (s:seq (Ty m)), i <= size s -> m |- map (@tsubst _ s _) E | post_compt (@tsubst _ s _) S |e- etsubst s e ::: tsubst s t).
apply @Typing_rect => i env se t.
- move => m l n s L. simpl. apply TvVAR. rewrite nth_error_map. by rewrite l.
- move => t' l e e'. rewrite e'. clear t e'. move => m s L. simpl. apply: (TvLOC _ _ (refl_equal _)).
  rewrite post_comp_simpl. by rewrite e.
- move => n e. rewrite e. clear t e. move => m s L. simpl. by apply TvINT.
(* - move => t0 t1 b e. rewrite e. clear t e. move => de IH m s L. simpl. apply: (TvLAMBDA (refl_equal _)).
  by apply IH.*)
- move => e t' e'. rewrite e'. clear t e'. move => D IH m s L. simpl. apply: (TvTLAM (refl_equal _)).
  specialize (IH m.+1). rewrite map_map. specialize (IH (TVar (ltn0Sn m):: map (@tshiftL 0 1 _) s)). simpl in IH.
  rewrite size_map in IH. specialize (IH L). rewrite map_map in IH.
  apply (tsubst_Eeq IH) ; clear IH.
  + apply eq_map. move => t. simpl.
    rewrite <- (@tsubst_shiftL' _ t 0 1 _ ((TVar (ltn0Sn m) :: map (@tshiftL 0 1 _) s))) ; first by [].
    * by rewrite take0. simpl. by do 2 rewrite drop0.
  + unfold post_compt. rewrite post_comp_comp. rewrite post_comp_comp. apply post_comp_eq. move => x. simpl.
    rewrite <- (@tsubst_shiftL' _ x 0 1 _ ((TVar (ltn0Sn m) :: map (@tshiftL 0 1 _) s))) ; first by [].
    by rewrite take0. simpl. by do 2 rewrite drop0.
- move => a t0 b e. rewrite e ; clear e t. move => db IH m s L. simpl. apply (TvLAMBDA (refl_equal _)).
  by apply IH.
- move => e. rewrite e. clear t e. move => m s L. by apply TvUNIT.
- move => t0 t1 v0 v1 e. rewrite e. clear t e. move => dv0 IH0 dv1 IH1 m s L. simpl.
  by apply: (TvP (refl_equal _)) ; [apply IH0 | apply IH1].
- move => t0 t1 v d IH e. rewrite e ; clear t e. simpl. move => m s L. by apply (TvINL (IH _ _ L)).
- move => t0 t1 v d IH e. rewrite e ; clear t e. simpl. move => m s L. by apply (TvINR (IH _ _ L)).
- move => t0 v d IH e. rewrite e. clear t e. move => m s L. simpl. apply: (TvFOLD _ (refl_equal _)).
  specialize (IH m).
  rewrite tsubst_map. simpl. rewrite map_map. specialize (IH s L). rewrite tsubst_map in IH.
  simpl in IH. have e:map (fun x : Ty m =>
                       tsubst (Mu (tsubst (TVar (ltn0Sn m) :: map (@tshiftL 0 1 _) s) t0) :: idsub 0 m) (tshiftL 0 1 x)) s =
                      map id s.
    apply eq_map. move => x. simpl. clear IH.
    by rewrite (@tsubst_shiftLW _ _ x _ _ _ (idsub 0 m)) ; simpl ; try rewrite take0 ; first by rewrite (tsubst_id x).
  rewrite e. clear e. rewrite map_id.
  rewrite (tsubst_ext t0 _ (s':=Mu
                (tsubst
                   (TVar (n:=m.+1) (i:=0) (ltn0Sn m) :: map (@tshiftL 0 1 _) s)
                   t0) :: map (@tsubst _ s _) (idsub 0 i))) ; first by [].
  case ; first by []. simpl. move => n X.
  rewrite (nth_map Unit) ; last by rewrite size_idsub.
  by rewrite (@nth_idsub i 0 n X).
(* - move => v d IH m s L. simpl. apply TvVOID. by apply IH.*)
- move => v d IH m s L. simpl. apply TeVAL. by apply IH.
- move => e0 e1 t0 d0 IH0 d1 IH1 m s L. simpl. by apply (TeLET (IH0 _ _ L) (IH1 _ _ L)).
- move => t0 v d IH m s L. simpl. by apply: (TvFST (IH _ _ _)).
- move => t0 v d IH m s L. simpl. by apply: (TvSND (IH _ _ _)).
- move => op v e. rewrite e. clear t e. move => d IH m s L. simpl.
  by apply: (TvOP _ (refl_equal _) (IH _ _ L)).
- move => t0 v d IH e. rewrite e. clear t e. move => m s L. simpl. apply: (TvUNFOLD (IH _ _ L) _). fold tsubst.
  do 2 rewrite tsubst_map. simpl. rewrite map_map. apply tsubst_ext.
  case ; first by []. move => j X. simpl. rewrite (nth_map Unit) ; last by rewrite (size_idsub 0).
  rewrite (nth_map Unit) ; last by apply (@ssrnat.leq_trans i j.+1 _ X L).
  rewrite (nth_idsub (i:=i) 0 X). have a:= (@tsubst_shiftLW _ _ (nth Unit s j) _ _ _ (idsub 0 m)).
  specialize (a 1 0). rewrite a ; [by rewrite tsubst_id | by do 2 rewrite take0 | by []].
- move => v t0 d IH e. rewrite e ; clear t e. simpl. move => m s L. by apply (TvREF (IH _ _ L)).
- move => v d IH m s L. simpl. apply TvBANG. by apply (IH _ _ L).
- move => v0 v1 t0 d0 IH0 d1 IH1 e. rewrite e ; clear t e. move => m s L.
  by apply: (TvASSIGN (IH0 _ _ L) (IH1 _ _ L) (refl_equal _)).
- move => t0 v0 v1 d0 IH0 d1 IH1 m s L. simpl. by apply (TeAPP (IH0 _ _ L) (IH1 _ _ L)).
- move => v t0 t1 d IH e. rewrite e ; clear t e. move => m s L. simpl. apply (TeTAPP (IH _ _ L)). fold tsubst.
  do 2 rewrite tsubst_map. simpl. rewrite map_map. apply tsubst_ext. case ; first by [].
  move => j X. simpl. rewrite (nth_map Unit) ; last by apply (@ssrnat.leq_trans _ j.+1 _ X L).
  rewrite (nth_map Unit) ; last by rewrite (size_idsub 0 i).
  rewrite (@tsubst_shiftLW 1 _ (nth Unit s j) 0 _ _ (idsub 0 m)) ; [rewrite tsubst_id | by do 2 rewrite take0 | by []].
  by rewrite (@nth_idsub i 0 j X).
- move => v e0 e1 t0 t1 dv IHv d0 IH0 d1 IH1 m s L. simpl.
  by apply (TeCASE (IHv _ _ L) (IH0 _ _ L) (IH1 _ _ L)).
Qed.

Definition tsubstV_deriv i E S t := fst (@tsubst_deriv i E S t).
Definition tsubstE_deriv i E S t := snd (@tsubst_deriv i E S t).

Fixpoint shiftV k i n (v:Value n) : Value n:=
match v with
| VAR j => if j < k then VAR j else VAR (j+i)
| LOC j => LOC j
| INT j => INT j
| TLAM e => TLAM (shiftE k i e)
| LAM t e => LAM t (shiftE k.+1 i e)
(*| FIX t0 t1 e => FIX t0 t1 (shiftE k.+2 i e)*)
| UNIT => UNIT
| P v0 v1 => P (shiftV k i v0) (shiftV k i v1)
| INL t v => INL t (shiftV k i v)
| INR t v => INR t (shiftV k i v)
| FOLD t v => FOLD t (shiftV k i v)
(* | VOID t v => VOID t (shiftV k i v)*)
end
with shiftE k i n (e:Exp n) : Exp n :=
match e with
| VAL v => VAL (shiftV k i v)
| LET e0 e1 => LET (shiftE k i e0) (shiftE k.+1 i e1)
| FST v => FST (shiftV k i v)
| SND v => SND (shiftV k i v)
| OP op v => OP op (shiftV k i v)
| UNFOLD v => UNFOLD (shiftV k i v)
| REF v => REF (shiftV k i v)
| BANG v => BANG (shiftV k i v)
| ASSIGN v0 v1 => ASSIGN (shiftV k i v0) (shiftV k i v1)
| APP v0 v1 => APP (shiftV k i v0) (shiftV k i v1)
| TAPP v t => TAPP (shiftV k i v) t
| CASE v e0 e1 => CASE (shiftV k i v) (shiftE k.+1 i e0) (shiftE k.+1 i e1)
end.

Fixpoint substV i (s:seq (Value i)) (v:Value i) : Value i :=
match v with
| VAR j => nth (@UNIT _) s j
| LOC j => LOC j
| INT j => INT j
| TLAM e => TLAM (substE (map (@vtsubst _ (drop 1 (idsub 0 i.+1)) _) s) e)
| LAM t e => LAM t (substE (VAR 0 :: (map (@shiftV 0 1 _) s)) e)
(*| FIX t0 t1 e => FIX t0 t1 (substE (VAR 0 :: VAR 1 :: (map (@shiftV 0 2 _) s)) e)*)
| UNIT => UNIT
| P v0 v1 => P (substV s v0) (substV s v1)
| INL t v => INL t (substV s v)
| INR t v => INR t (substV s v)
| FOLD t v => FOLD t (substV s v)
(*| VOID t v => VOID t (substV s v)*)
end
with substE i (s:seq (Value i)) (e:Exp i) : Exp i :=
match e with
| VAL v => VAL (substV s v)
| LET e0 e1 => LET (substE s e0) (substE (VAR 0 :: map (@shiftV 0 1 _) s) e1)
| FST v => FST (substV s v)
| SND v => SND (substV s v)
| OP op v => OP op (substV s v)
| UNFOLD v => UNFOLD (substV s v)
| REF v => REF (substV s v)
| BANG v => BANG (substV s v)
| ASSIGN v0 v1 => ASSIGN (substV s v0) (substV s v1)
| APP v0 v1 => APP (substV s v0) (substV s v1)
| TAPP v t => TAPP (substV s v) t
| CASE v e0 e1 => CASE (substV s v) (substE (VAR 0 :: map (@shiftV 0 1 _) s) e0) (substE (VAR 0 :: map (@shiftV 0 1 _) s) e1)
end.

Definition weakenV i n (x:Value n) := shiftV 0 i x.
Definition weakenE i n (x:Exp n) := shiftE 0 i x.

Definition env_keq n k (E E':seq (Ty n)) j i := (i < k -> nth_error E' i = nth_error E i) /\ (k <= i -> nth_error E' (i+j) = nth_error E i).

Lemma weakening_deriv j i E S t :
   (forall v, i |- E | S |v- v ::: t -> forall k E', (forall i, env_keq k E E' j i) -> i |- E' | S |v- shiftV k j v ::: t) *
   (forall e, i |- E | S |e- e ::: t -> forall k E', (forall i, env_keq k E E' j i) -> i |- E' | S |e- shiftE k j e ::: t).
move => j. apply @Typing_rect => i env se t.
- move => m e k E' X. simpl. case_eq (m < k) => Y ; first by apply TvVAR ; rewrite (proj1 (X m) Y).
  rewrite ltnNge in Y. have YY:=negbFE Y. clear Y. by apply TvVAR ; rewrite (proj2 (X m) YY).
- move => t' l e e'. rewrite e'. clear t e'. move => k E' X. simpl. by apply (TvLOC _ e (refl_equal _)).
- move => n e. rewrite e. clear t e. move => k E' X. simpl. by apply TvINT.
- move => e t' e'. rewrite e'. clear e' t. move => D IH k s E. simpl. apply (TvTLAM (refl_equal _)).
  apply IH. move => i'. specialize (E i').  split. move => L. destruct E as [E X]. specialize (E L).
  rewrite nth_error_map. rewrite nth_error_map. by rewrite E.
  move => L. destruct E as [_ E]. specialize (E L). rewrite nth_error_map. rewrite nth_error_map. by rewrite E.
(*- move => t0 t1 b e. rewrite e. clear t e. move => db IH k E' X. simpl. apply (TvLAMBDA (refl_equal _)).
  apply IH. case ; first by split. by apply X.*)
- move => a b body e. rewrite e. clear t e. move => db IH k E' X. simpl. apply (TvLAMBDA (refl_equal _)).
  apply IH. case ; first by split. by apply X.
- move => e. rewrite e. clear e t. move => k E' IH. simpl. by apply TvUNIT.
- move => t0 t1 v0 v1 e. rewrite e. clear t e. move => d0 IH0 d1 IH1 k E' X. simpl.
  by apply (TvP (refl_equal _)) ; [apply IH0 | apply IH1] ; apply X.
- move => t0 t1 b d IH e. rewrite e ; clear t e. move => k E' X. simpl. by apply (TvINL (IH _ _ X)).
- move => t0 t1 b d IH e. rewrite e ; clear t e. move => k E' X. simpl. by apply (TvINR (IH _ _ X)).
- unfold addn. unfold addn_rec. simpl. move => t' v d IH e. rewrite e. clear e t. move => k E' X.
  by apply: (TvFOLD (IH _ _ X) (refl_equal _)).
(*- move => v d IH k E' X. simpl. by apply (TvVOID _ (IH _ _ X)).*)
- move => v d IH k E' X. simpl. by apply (TeVAL (IH _ _ X)).
- move => e0 e1 t' d0 IH0 d1 IH1 k E' X. simpl. apply: (TeLET (IH0 _ _ X) (IH1 _ _ _)). case ; by [split | apply X].
- move => t' v d IH k E' X. simpl. by apply: (TvFST (IH _ _ X)).
- move => t' v d IH k E' X. simpl. by apply: (TvSND (IH _ _ X)).
- move => op v e. rewrite e ; clear t e. move => d IH k E' X. simpl. by apply (TvOP op (refl_equal _) (IH _ _ X)).
- move => t' v d IH e. rewrite e. clear e t. move => k E' X. simpl. by apply (TvUNFOLD (IH _ _ X) (refl_equal _)).
- move => v t' d IH e. rewrite e. clear e t. move => k E' X. simpl. by apply (TvREF (IH _ _ X) (refl_equal _)).
- move => v d IH k E' X. simpl. by apply (TvBANG (IH _ _ X)).
- move => v0 v1 t' d0 IH0 d1 IH1 e. rewrite e. clear e t. move => k E' X. simpl.
  by apply (TvASSIGN (IH0 _ _ X) (IH1 _ _ X) (refl_equal _)).
- move => t0 v0 v1 d0 IH0 d1 IH1 k E' X. simpl. by apply (TeAPP (IH0 _ _ X) (IH1 _ _ X)).
- unfold addn. unfold addn_rec. simpl. move => v t0 t1 d IH e. rewrite e. clear t e. move => k E' X.
  by apply (TeTAPP (IH _ _ X)).
- move => v e0 e1 t0 t1 dv IHv d0 IH0 d1 IH1 k E' X. simpl. apply (TeCASE (IHv _ _ X)) ;
  try apply IH0 ; try apply IH1 ; case ; by [split | apply X].
Qed.

Definition typing_shiftV j i E S t := fst (@weakening_deriv j i E S t).
Definition typing_shiftE j i E S t := snd (@weakening_deriv j i E S t).

Lemma nth_error_some_nth T (l:seq T) m e x : nth_error l m = Some e -> nth x l m = e.
move => T. elim ; first by [].
move => e s IH. case ; last by apply IH. by simpl ; move => e' _ ; case.
Qed.

Lemma post_compt_eq T T' T'' (f g : T' -> T'') : f =1 g -> @post_compt T _ _ f =1 post_compt g.
move => T T' T'' f g e. unfold post_compt. move => x. simpl. apply post_comp_eq. move => y. simpl.
by rewrite e.
Qed.

Lemma subst_deriv i E S t :
   (forall v, i |- E | S |v- v ::: t -> forall (s:seq (Value i)) E' (d:forall j, i |- E' | S |v- nth UNIT s j ::: nth Unit E j), i |- E' | S |v- substV s v ::: t) *
   (forall e, i |- E | S |e- e ::: t -> forall (s:seq (Value i)) E' (d:forall j, i |- E' | S |v- nth UNIT s j ::: nth Unit E j), i |- E' | S |e- substE s e ::: t).
apply @Typing_rect => i env se t.
- move => m e s E' X. simpl. specialize (X m). by rewrite (nth_error_some_nth Unit e) in X.
- move => t' l e e'. rewrite e'. clear t e'. move => s E' X. simpl. by apply (TvLOC _ e).
- move => n e. rewrite e. clear t e. move => s E' X. by apply TvINT.
- move => e t' e'. rewrite e'. clear t e'. move => D IH s E' X. simpl. apply (TvTLAM (refl_equal _)).
  apply IH. move => j. have a:= @tsubstV_deriv _ _ _ _ _ (X j) i.+1 (drop 1 (idsub 0 i.+1)).
  rewrite size_drop in a. rewrite (size_idsub 0 i.+1) in a. rewrite subn1 in a. specialize (a (leqnn i)).
  have x:=fun x => @tsubst_idsubL 1 i x 0 (drop 1 (idsub 0 (i.+1))).
  have xx:@tsubst _ (drop 1 (idsub 0 i.+1)) i =1 @tshiftL 0 1 i. move => xx. apply x ; first by [].
    move => jj _. by rewrite nth_drop. clear x.
  rewrite <- (eq_map xx). rewrite <- (@post_compt_eq _ (Ty i) _ _ (@tshiftL 0 1 _) xx).
  rewrite <- (eq_map xx).
  case_eq (j < size s) => Y.
  + rewrite (nth_map UNIT _ _ Y). case_eq (j < size env) => Z ; first by rewrite (nth_map Unit _ _ Z); by apply a.
    rewrite ltnNge in Z. have ZZ:=negbFE Z.
    rewrite (nth_default Unit) ; last by rewrite size_map. rewrite (nth_default Unit) in a ; last by []. by apply a.
  + rewrite ltnNge in Y. have YY:=negbFE Y. rewrite (nth_default UNIT) ; last by rewrite size_map.
    rewrite (nth_default UNIT) in a ; last by []. simpl in a.
    case_eq (j < size env) => Z ; first by rewrite (nth_map Unit _ _ Z); by apply a.
    rewrite ltnNge in Z. have ZZ:=negbFE Z.
    rewrite (nth_default Unit) ; last by rewrite size_map. rewrite (nth_default Unit) in a ; last by []. by apply a.

- move => a b body e. rewrite e. clear t e. move => d IH s E' X. simpl. apply (TvLAMBDA (refl_equal _)).
  apply IH. case ;first by apply TvVAR. simpl. move => j.
  case_eq (j < size s) => Y.
  + rewrite (nth_map UNIT _ _ Y). apply (typing_shiftV (X j)). case ; first by split. case ; first by split.
    move => n. split ; [by [] | by rewrite addnC].
  + rewrite ltnNge in Y. have YY:=negbFE Y. clear Y. rewrite (nth_default UNIT) ; last by rewrite size_map.
    specialize (X j). rewrite (nth_default UNIT YY) in X. apply TvUNIT. by inversion X.
- move => e. rewrite e. simpl. by intros ; apply TvUNIT.
- move => a b v0 v1 e. rewrite e. clear t e. move => d0 IH0 d1 IH1 s E' X. simpl.
  by apply (TvP (refl_equal _) (IH0 _ _ X) (IH1 _ _ X)).
- move => a b v d IH e. rewrite e. clear e t. move => s E' X. simpl. by apply (TvINL (IH _ _ X)).
- move => a b v d IH e. rewrite e. clear e t. move => s E' X. simpl. by apply (TvINR (IH _ _ X)).
- unfold addn. unfold addn_rec. simpl. move => t' v d IH e. rewrite e ; clear e t.
  move => s E' X. by apply (TvFOLD (IH _ _ X)).
(*- move => v d IH s E' X. simpl. by apply (TvVOID _ (IH _ _ X)).*)
- move => v d IH s E' X. simpl. apply (TeVAL (IH _ _ X)).
- move => e0 e1 t' d0 IH0 d1 IH1 s E' X. simpl. apply (TeLET (IH0 _ _ X)). apply IH1. case ; first by apply TvVAR.
  simpl. move => j. case_eq (j < size s) => Y.
  + rewrite (nth_map UNIT _ _ Y). apply (typing_shiftV (X j)). case ; first by split.
    move => n ; split ; first by []. by rewrite addnC.
  + rewrite ltnNge in Y. have YY:=negbFE Y. clear Y. rewrite (nth_default UNIT) ; last by rewrite size_map.
    specialize (X j). apply TvUNIT. rewrite (nth_default UNIT YY) in X. by inversion X.
- move => a v d IH s E' X. simpl. by apply (TvFST (IH _ _ X)).
- move => a v d IH s E' X. simpl. by apply (TvSND (IH _ _ X)).
- move => op v e. rewrite e. clear e t. move => d IH s E' X. simpl. by apply: (TvOP _ _ (IH _ _ X)).
- move => a v d IH e. rewrite e. clear e t. move => s E' X. simpl. by apply (TvUNFOLD (IH _ _ X)).
- move => v t' d IH e. rewrite e. clear e t. move => s E' X. simpl. by apply (TvREF (IH _ _ X)).
- move => v d IH s E' X. simpl. by apply (TvBANG (IH _ _ X)).
- move => v0 v1 t' d0 IH0 d1 IH1 e. rewrite e. clear e t. move => s E' X.
  simpl. by apply (TvASSIGN (IH0 _ _ X) (IH1 _ _ X)).
- move => a v0 v1 d0 IH0 d1 IH1 s E' X. simpl. by apply (TeAPP (IH0 _ _ X) (IH1 _ _ X)).
- unfold addn. unfold addn_rec. simpl. move => v a b d IH e. rewrite e. clear e t.
  move => s E' X. by apply (TeTAPP (IH _ _ X)).
- move => v e0 e1 a b dv IHv d0 IH0 d1 IH1 s E' X. simpl.
  apply: (TeCASE (IHv _ _ X) (IH0 _ _ _) (IH1 _ _ _)) ; case ; [by apply TvVAR | idtac | by apply TvVAR | idtac ].
  + move => j. simpl.
    case_eq (j < size s) => Y.
    * rewrite (nth_map UNIT _ _ Y). apply (typing_shiftV (X j)). case ; first by split.
      move => n ; split ; first by []. by rewrite addnC.
    * rewrite ltnNge in Y. have YY:=negbFE Y. clear Y. rewrite (nth_default UNIT) ; last by rewrite size_map.
      specialize (X j). apply TvUNIT. rewrite (nth_default UNIT YY) in X. by inversion X.
  + move => j. simpl.
    case_eq (j < size s) => Y.
    * rewrite (nth_map UNIT _ _ Y). apply (typing_shiftV (X j)). case ; first by split.
      move => n ; split ; first by []. by rewrite addnC.
    * rewrite ltnNge in Y. have YY:=negbFE Y. clear Y. rewrite (nth_default UNIT) ; last by rewrite size_map.
      specialize (X j). apply TvUNIT. rewrite (nth_default UNIT YY) in X. by inversion X.
Qed.

Definition typing_substV i E S t := fst (@subst_deriv i E S t).
Definition typing_substE i E S t := snd (@subst_deriv i E S t).

Lemma Typing_unique i E S t:
   (forall v, i |- E | S |v- v ::: t -> forall t', i |- E | S |v- v ::: t' -> t = t') /\
   (forall e, i |- E | S |e- e ::: t -> forall t', i |- E | S |e- e ::: t' -> t = t').
apply (@Typing_ind) => i E S t.
- move => m e t' T. inversion T. rewrite e in H0. by inversion H0.
- move => t' l e e'. rewrite e'. clear t e'. move => t T. inversion T. rewrite H1. rewrite e in H0. by inversion H0.
- move => n e. rewrite e. clear e t. move => t' T. by inversion T.
- move => e t' e'. rewrite e'. clear t e'. move => D IH t D'. inversion D'. clear e0 H. rewrite H0. clear t H0 D'.
  by rewrite (IH _ X).
(*- move => a b e eq. rewrite eq. clear t eq. move => te IH t' T. inversion T. rewrite H1.
  specialize (IH _ H2). by rewrite IH.*)
- move => a b body eq. rewrite eq. clear t eq. move => te IH t' T. inversion T. specialize (IH _ X). by rewrite H0 ; rewrite <- IH.
- move => e. rewrite e. clear t e. move => t' T. inversion T. by rewrite H.
- move => a b v0 v1 e. rewrite e. clear t e. move => tv0 IH0 tv1 IH1 t' T. inversion T. rewrite H0.
  rewrite (IH0 _ X). by rewrite (IH1 _ X0).
- move => a b e te IH eq. rewrite eq. clear t eq. move => t' T. inversion T. by rewrite (IH _ X).
- move => a b e te IH eq. rewrite eq. clear t eq. move => t' T. inversion T. by rewrite (IH _ X).
- move => a v tv IH e. rewrite e. clear e t. move => t' T. inversion T. by rewrite H0.
(* - move => v d IH t' d'. by inversion d'.*)
- move => v d IH t' d'. inversion d'. by rewrite (IH _ X).
- move => e0 e1 t' d0 IH0 d1 IH1 t1 d'. inversion d'. specialize (IH0 _ X). rewrite <- IH0 in X0. by specialize (IH1 _ X0).
- move => a p te IH t' T. inversion T. specialize (IH _ X). by inversion IH.
- move => a p te IH t' T. inversion T. specialize (IH _ X). by inversion IH.
- move => op v0 e. rewrite e. clear t e. move => T0 IH0 t' T. by inversion T.
- move => a v tv IH e. rewrite e. clear e t. move => t' T. inversion T. rewrite H0.
  specialize (IH _ X). by inversion IH.
- move => v a d IH e. rewrite e. clear t e. move => t' d'. inversion d'. rewrite H0. by rewrite (IH _ X).
- move => v d IH t' d'. inversion d'. specialize (IH _ X). by inversion IH.
- move => v0 v1 a d0 IH0 d1 IH1 e. rewrite e. clear t e. move => t' T. by inversion T.
- move => t' v0 v1 d0 IH0 d1 IH1 t0 d'. inversion d'. specialize (IH0 _ X). by inversion IH0.
- move => v t0 t1 d IH e. rewrite e. clear e t. move => t' d'. inversion d'. specialize (IH _ X). inversion IH.
  by rewrite H0.
- move => v e0 e1 t0 t1 dv IHv d1 IH1 d2 IH2 t' d'. inversion d'. specialize (IHv _ X). inversion IHv.
  rewrite <- H3 in X0. by rewrite (IH1 _ X0).
Qed.

Definition typesV_unique i E S t := proj1 (@Typing_unique i E S t).
Definition typesE_unique i E S t := proj2 (@Typing_unique i E S t).

Definition ExpValue_rect n (P0 : forall n : nat, Value n -> Type) (P1 : forall n : nat, Exp n -> Type)
  f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20  :=
  (@Value_type2 P0 P1 f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 n,
   @Exp_type2 P0 P1 f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 n).

Lemma tsubst_shiftV i n : 
  (forall (x:Value n) k m (s:seq (Ty m)), vtsubst s (shiftV k i x) = shiftV k i (vtsubst s x)) /\
  (forall (x:Exp n) k m (s:seq (Ty m)), etsubst s (shiftE k i x) = shiftE k i (etsubst s x)).
move => i. apply (@ExpValue_ind) => n.
- move => k m s x. simpl. by case_eq (k < m) => C.
- by [].
- by [].
- move => e IH k m s. simpl. by rewrite IH.
- move => t e IH k m s. simpl. by rewrite IH.
(*- move => t0 t1 e IH k m s. simpl. by rewrite IH.*)
- by [].
- move => v0 IH0 v1 IH1 k m s. simpl. rewrite IH0. by rewrite (IH1).
- move => t v IH k m s. simpl. by rewrite IH.
- move => t v IH k m s. simpl. by rewrite IH.
- move => t v IH k m s. simpl. by rewrite IH.
- move => v IH k m s. simpl. by rewrite IH.
- move => v IH k m s. simpl. by rewrite IH.
- move => v IH k m s. simpl. by rewrite IH.
- move => op v IH k m s. simpl. by rewrite IH.
- move => v IH k m s. simpl. by rewrite IH.
- move => v IH k m s. simpl. by rewrite IH.
- move => v IH k m s. simpl. by rewrite IH.
- move => v0 IH0 v1 IH1 k m s. simpl. by rewrite -> IH0, -> IH1.
- move => e0 IH0 e1 IH1 k m s. simpl. by rewrite -> IH0, -> IH1.
- move => e0 IH0 e1 IH1 k m s. simpl. by rewrite -> IH0, -> IH1.
- move => v IH t k m s. simpl. by rewrite -> IH.
- move => v IH e0 IH0 e1 IH1 k m s. simpl. by rewrite -> IH, -> IH0, -> IH1.
Qed.

Definition vtsubst_shiftV i n := proj1 (@tsubst_shiftV i n).
Definition etsubst_shiftE i n := proj2 (@tsubst_shiftV i n).

Lemma shift_shift i i' n :
    (forall (x:Value n) k k', k <= k' -> shiftV (k'+i) i' (shiftV k i x) = shiftV k i (shiftV k' i' x)) /\
    (forall (x:Exp n) k k', k <= k' -> shiftE (k'+i) i' (shiftE k i x) = shiftE k i (shiftE k' i' x)).
move => i i'. apply ExpValue_ind => n.
- move => j k k' L. simpl. case_eq (j < k) => E.
  + rewrite (ssrnat.leq_trans E L). simpl. rewrite E. by rewrite (ssrnat.leq_trans (ssrnat.leq_trans E L) (leq_addr _ _)).
  + simpl. case_eq (j < k') => E'.
    * rewrite <- (ltn_add2r i) in E'. rewrite E'. simpl. by rewrite E.
    * rewrite <- (ltn_add2r i) in E'. rewrite E'. simpl. rewrite ltnNge in E. have e:=ssrnat.leq_trans (negbFE E) (leq_addr i' _).
      have e':=negbF e. rewrite <- ltnNge in e'. rewrite e'. clear. rewrite <- addnA. rewrite (addnC i i').
      by rewrite addnA.
- by [].
- by [].
- move => e IH k k' L. simpl. by rewrite IH.
- move => t e IH k k' L. simpl. f_equal. apply (IH k.+1 k'.+1 L).
(*- move => t0 t1 e IH k k' L. simpl. f_equal. apply (IH k.+2 k'.+2 L).*)
- by [].
- move => v0 IH0 v1 IH1 k k' L. simpl. by rewrite -> IH0, -> IH1.
- move => t v IH k k' L. simpl. by rewrite -> IH.
- move => t v IH k k' L. simpl. by rewrite -> IH.
- move => t v IH k k' L. simpl. by rewrite -> IH.
- move => v IH k k' L. simpl. by rewrite -> IH.
- move => v IH k k' L. simpl. by rewrite -> IH.
- move => v IH k k' L. simpl. by rewrite -> IH.
- move => op v IH k k' L. simpl. by rewrite -> IH.
- move => v IH k k' L. simpl. by rewrite -> IH.
- move => v IH k k' L. simpl. by rewrite -> IH.
- move => v IH k k' L. simpl. by rewrite -> IH.
- move => v0 IH0 v1 IH1 k k' L. simpl. by rewrite -> IH0, -> IH1.
- move => v0 IH0 v1 IH1 k k' L. simpl. rewrite (IH0 _ _ L). f_equal. by apply (IH1 k.+1 k'.+1 L).
- move => v0 IH0 v1 IH1 k k' L. simpl. by rewrite -> IH0, -> IH1.
- move => v IH t k k' L. simpl. by rewrite -> IH.
- move => v0 IH0 v1 IH1 e2 IH2 k k' L. simpl. rewrite -> (IH0 _ _ L). rewrite (IH1 k.+1 k'.+1 L).
  by rewrite (IH2 k.+1 k'.+1 L).
Qed.

Definition shiftV_shiftV i i' n := proj1 (@shift_shift i i' n).
Definition shiftE_shiftE i i' n := proj2 (@shift_shift i i' n).

Lemma subst_shift i n :
   (forall (t:Value n) k s' (s:seq (Value n)),
    map (@shiftV k i _) (take k s) = take k s' ->
    map (@shiftV k i _) (drop k s) = drop (k+i) s' ->
    substV s' (shiftV k i t) = shiftV k i (substV s t)) /\
   (forall (t:Exp n) k s' (s:seq (Value n)),
    map (@shiftV k i _) (take k s) = take k s' ->
    map (@shiftV k i _) (drop k s) = drop (k+i) s' ->
    substE s' (shiftE k i t) = shiftE k i (substE s t)).
move => i. apply ExpValue_ind => n.
- move => m k s' s E E'. simpl.
  case_eq (m < k) => C.
  + simpl. have e:=f_equal (fun x => nth UNIT x m) E.
    rewrite map_take in e. do 2 rewrite (nth_take UNIT C) in e. rewrite <- e.
    case_eq (m < size s) => C' ; first by  rewrite (nth_map UNIT _ _ C').
    rewrite ltnNge in C'. have C0:=negbFE C'. clear C'.
    rewrite nth_default ; last by rewrite size_map. by rewrite (nth_default UNIT C0).
  + rewrite ltnNge in C. have C0 := negbFE C. clear C.
    have e:=f_equal (fun x => nth UNIT x (m - k)) E'. clear E E'. rewrite map_drop in e.
    do 2 rewrite nth_drop in e. simpl. rewrite (subnKC C0) in e. rewrite addnC in e. rewrite addnA in e.
    rewrite (subnK C0) in e. rewrite <- e. clear e.
    case_eq (m < size s) => C' ; first by  rewrite (nth_map UNIT _ _ C').
    rewrite ltnNge in C'. have C:=negbFE C'. clear C'.
    rewrite nth_default ; last by rewrite size_map. by rewrite (nth_default UNIT C).
- by [].
- by [].
- move => e IH k s' s E E'. simpl. f_equal. apply IH.
  + rewrite <- map_take. rewrite map_map. rewrite <- map_take. rewrite <- E. clear.
    rewrite map_map. apply eq_map. move => x. simpl. by rewrite vtsubst_shiftV.
  + rewrite <- map_drop. rewrite map_map. rewrite <- map_drop. rewrite <- E'. clear.
    rewrite map_map. apply eq_map. move => x. simpl. by rewrite vtsubst_shiftV.
 - move => t e IH k s' s E E'. simpl. f_equal. apply IH ; simpl ; f_equal.
  + rewrite <- map_take. rewrite map_map. rewrite <- map_take. rewrite <- E. clear.
    rewrite map_map. apply eq_map. move => x. simpl. rewrite <- (shiftV_shiftV 1 i) ;  by try rewrite addnC.
  + rewrite <- map_drop. rewrite map_map. rewrite <- map_drop. fold addn. rewrite <- E'. clear.
    rewrite map_map. apply eq_map. move => x. simpl. rewrite <- (shiftV_shiftV 1 i) ;  by try rewrite addnC.
(*- move => t0 t1 e IH k s' s E E'. simpl. f_equal. apply IH ; simpl ; f_equal ; f_equal.
  + rewrite <- map_take. rewrite map_map. rewrite <- map_take. rewrite <- E. clear.
    rewrite map_map. apply eq_map. move => x. simpl. rewrite <- (shiftV_shiftV 2 i) ;  by try rewrite addnC.
  + rewrite <- map_drop. rewrite map_map. rewrite <- map_drop. fold addn. rewrite <- E'. clear.
    rewrite map_map. apply eq_map. move => x. simpl. rewrite <- (shiftV_shiftV 2 i) ;  by try rewrite addnC.*)
- by [].
- move => v0 IH0 v1 IH1 k s' s E E'. simpl. rewrite (IH0 _ _ _ E E'). by rewrite (IH1 _ _ _ E E').
- move => t v IH k s' s E E'. simpl. by rewrite (IH _ _ _ E E').
- move => t v IH k s' s E E'. simpl. by rewrite (IH _ _ _ E E').
- move => t v IH k s' s E E'. simpl. by rewrite (IH _ _ _ E E').
- move => v IH k s' s E E'. simpl. by rewrite (IH _ _ _ E E').
- move => v IH k s' s E E'. simpl. by rewrite (IH _ _ _ E E').
- move => v IH k s' s E E'. simpl. by rewrite (IH _ _ _ E E').
- move => op v IH k s' s E E'. simpl. by rewrite (IH _ _ _ E E').
- move => v IH k s' s E E'. simpl. by rewrite (IH _ _ _ E E').
- move => v IH k s' s E E'. simpl. by rewrite (IH _ _ _ E E').
- move => v IH k s' s E E'. simpl. by rewrite (IH _ _ _ E E').
- move => v0 IH0 v1 IH1 k s' s E E'. simpl. rewrite (IH0 _ _ _ E E'). by rewrite (IH1 _ _ _ E E').
- move => e0 IH0 e1 IH1 k s' s E E'. simpl. rewrite (IH0 _ _ _ E E').
  f_equal. apply IH1 ; simpl ; f_equal.
  + rewrite <- map_take. rewrite map_map. rewrite <- map_take. rewrite <- E. clear.
    rewrite map_map. apply eq_map. move => x. simpl. rewrite <- (shiftV_shiftV 1 i) ;  by try rewrite addnC.
  + rewrite <- map_drop. rewrite map_map. rewrite <- map_drop. fold addn. rewrite <- E'. clear.
    rewrite map_map. apply eq_map. move => x. simpl. rewrite <- (shiftV_shiftV 1 i) ;  by try rewrite addnC.
- move => v0 IH0 v1 IH1 k s' s E E'. simpl. rewrite (IH0 _ _ _ E E'). by rewrite (IH1 _ _ _ E E').
- move => v IH t k s' s E E'. simpl. by rewrite (IH _ _ _ E E').
- move => e0 IH0 e1 IH1 e2 IH2 k s' s E E'. simpl. rewrite (IH0 _ _ _ E E').
  f_equal. apply IH1 ; simpl ; f_equal.
  + rewrite <- map_take. rewrite map_map. rewrite <- map_take. rewrite <- E. clear.
    rewrite map_map. apply eq_map. move => x. simpl. rewrite <- (shiftV_shiftV 1 i) ;  by try rewrite addnC.
  + rewrite <- map_drop. rewrite map_map. rewrite <- map_drop. fold addn. rewrite <- E'. clear.
    rewrite map_map. apply eq_map. move => x. simpl. rewrite <- (shiftV_shiftV 1 i) ;  by try rewrite addnC.
  apply IH2 ; simpl ; f_equal.
  + rewrite <- map_take. rewrite map_map. rewrite <- map_take. rewrite <- E. clear.
    rewrite map_map. apply eq_map. move => x. simpl. rewrite <- (shiftV_shiftV 1 i) ;  by try rewrite addnC.
  + rewrite <- map_drop. rewrite map_map. rewrite <- map_drop. fold addn. rewrite <- E'. clear.
    rewrite map_map. apply eq_map. move => x. simpl. rewrite <- (shiftV_shiftV 1 i) ;  by try rewrite addnC.
Qed.

Definition substV_shiftV i n := proj1 (@subst_shift i n).
Definition substE_shiftE i n := proj2 (@subst_shift i n).

Lemma free_varW n : (forall v:Value n, forall l l', free_varV v l -> (forall i, i \in l -> i \in l') -> free_varV v l') /\
                    (forall e:Exp n, forall l l', free_varE e l -> (forall i, i \in l -> i \in l') -> free_varE e l').
apply ExpValue_ind => n.
- move => j l l'. simpl. move => I X. by apply (X _ I).
- by [].
- by [].
- move => e IH l l'. simpl. move => F X. by apply (IH l l' F X).
- move => t e IH l l'. simpl. move => F X. specialize (IH (0 :: map S l) (0 :: map S l') F).
  apply IH. move => j. case: j ; first by do 2 rewrite in_cons. move => j. do 2 rewrite in_cons.
  rewrite (mem_map succn_inj l j). rewrite (mem_map succn_inj l' j). simpl. by apply X.
- by [].
- move => v0 IH0 v1 IH1 l l' F X. simpl. simpl in F. rewrite (IH0 _ _ (proj1 (andP F)) X).
  by rewrite (IH1 _ _ (proj2 (andP F)) X).
- move => t v IH l l' F X. simpl. simpl in F. by apply (IH _ _ F X).
- move => t v IH l l' F X. simpl. simpl in F. by apply (IH _ _ F X).
- move => t v IH l l' F X. simpl. simpl in F. by apply (IH _ _ F X).
- move => v IH l l' F X. simpl. simpl in F. by apply (IH _ _ F X).
- move => v IH l l' F X. simpl. simpl in F. by apply (IH _ _ F X).
- move => v IH l l' F X. simpl. simpl in F. by apply (IH _ _ F X).
- move => op v IH l l' F X. simpl. simpl in F. by apply (IH _ _ F X).
- move => v IH l l' F X. simpl. simpl in F. by apply (IH _ _ F X).
- move => v IH l l' F X. simpl. simpl in F. by apply (IH _ _ F X).
- move => v IH l l' F X. simpl. simpl in F. by apply (IH _ _ F X).
- move => v0 IH0 v1 IH1 l l' F X. simpl. simpl in F. rewrite (IH0 _ _ (proj1 (andP F)) X).
  by rewrite (IH1 _ _ (proj2 (andP F)) X).
- move => e0 IH0 e1 IH1 l l'. simpl. move => F X. rewrite (IH0 _ _ (proj1 (andP F)) X).
  specialize (IH1 (0 :: map S l) (0 :: map S l') (proj2 (andP F))). simpl.
  apply IH1. move => j. case: j ; first by do 2 rewrite in_cons. move => j. do 2 rewrite in_cons.
  rewrite (mem_map succn_inj l j). rewrite (mem_map succn_inj l' j). simpl. by apply X.
- move => v0 IH0 v1 IH1 l l' F X. simpl. simpl in F. rewrite (IH0 _ _ (proj1 (andP F)) X).
  by rewrite (IH1 _ _ (proj2 (andP F)) X).
- move => v0 IH0 t l l' F X. simpl. simpl in F. by rewrite (IH0 _ _ F X).
- move => e0 IH0 e1 IH1 e2 IH2 l l'. simpl. move => F X. rewrite (IH0 _ _ (proj1 (andP (proj1 (andP F)))) X).
  specialize (IH1 (0 :: map S l) (0 :: map S l') (proj2 (andP (proj1 (andP F))))). simpl.
  specialize (IH2 (0 :: map S l) (0 :: map S l') (proj2 (andP F))).
  rewrite IH1. simpl. apply IH2.
  + move => j. case: j ; first by do 2 rewrite in_cons. move => j. do 2 rewrite in_cons.
    rewrite (mem_map succn_inj l j). rewrite (mem_map succn_inj l' j). simpl. by apply X.
  + move => j. case: j ; first by do 2 rewrite in_cons. move => j. do 2 rewrite in_cons.
    rewrite (mem_map succn_inj l j). rewrite (mem_map succn_inj l' j). simpl. by apply X.
Qed.

Definition free_varVW n := proj1 (@free_varW n).
Definition free_varEW n := proj2 (@free_varW n).

Lemma free_var_exists n : (forall v:Value n, exists l, free_varV v l) /\ (forall e:Exp n, exists l, free_varE e l).
apply ExpValue_ind => n.
- move => j. exists [:: j]. simpl. rewrite in_cons. by rewrite eq_refl.
- move => j. by exists [::].
- move => j. by exists [::].
- move => j. case => l F. exists l. by apply F.
- move => t e. case => l F. simpl. exists (map (fun x => x.-1) l). apply: (free_varEW F).
  case ; first by rewrite in_cons ; rewrite eq_refl.
  move => i I. rewrite in_cons. simpl. rewrite map_map. clear F. elim: l I ; first by []. simpl. case.
    + simpl => s IH. rewrite in_cons. simpl. move => A. rewrite in_cons. rewrite (IH A). by rewrite orbT.
    + simpl. move => j s IH. rewrite in_cons. rewrite in_cons. move => X.
      destruct (orP X) as [A | A] ; first by rewrite A. rewrite (IH A). by rewrite orbT.
- by exists [::].
- move => v0. case => l0 IH0 v1. case => l1 IH1. exists (l0 ++ l1). simpl.
  rewrite (free_varVW IH0) ; first rewrite (free_varVW IH1) ; first by [].
  + move => i. rewrite mem_cat. move => A. rewrite A. by rewrite orbT.
  + move => i. rewrite mem_cat. move => A. by rewrite A.
- move => t v. case => l IH. by exists l.
- move => t v. case => l IH. by exists l.
- move => t v. case => l IH. by exists l.
- move => v. case => l IH. by exists l.
- move => v. case => l IH. by exists l.
- move => v. case => l IH. by exists l.
- move => op v. case => l IH. by exists l.
- move => v. case => l IH. by exists l.
- move => v. case => l IH. by exists l.
- move => v. case => l IH. by exists l.
- move => v0. case => l0 IH0 v1. case => l1 IH1. exists (l0 ++ l1). simpl.
  rewrite (free_varVW IH0) ; first rewrite (free_varVW IH1) ; first by [].
  + move => i. rewrite mem_cat. move => A. rewrite A. by rewrite orbT.
  + move => i. rewrite mem_cat. move => A. by rewrite A.
- move => e0. case => l F e1. case => l' F'. simpl. exists (l ++ map (fun x => x.-1) l').
  rewrite (free_varEW F) ; first rewrite (free_varEW F') ; first by [].
  + case ; first by rewrite in_cons ; rewrite eq_refl.
    move => i I. rewrite in_cons. simpl. rewrite map_cat. rewrite mem_cat. rewrite map_map.
    clear F F'. have T:(i.+1 \in map (fun x : nat => x.-1.+1) l').
    elim: l' I ; first by []. simpl. case.
    + simpl => s IH. rewrite in_cons. simpl. move => A. rewrite in_cons. rewrite (IH A). by rewrite orbT.
    + simpl. move => j s IH. rewrite in_cons. rewrite in_cons. move => X.
      destruct (orP X) as [A | A] ; first by rewrite A. rewrite (IH A). by rewrite orbT.
    rewrite T. by rewrite orbT.
  + move => i A. rewrite mem_cat. by rewrite A.
- move => v0. case => l0 IH0 v1. case => l1 IH1. exists (l0 ++ l1). simpl.
  rewrite (free_varVW IH0) ; first rewrite (free_varVW IH1) ; first by [].
  + move => i. rewrite mem_cat. move => A. rewrite A. by rewrite orbT.
  + move => i. rewrite mem_cat. move => A. by rewrite A.
- move => v0. case => l0 IH0 t. exists l0. simpl. by apply IH0.
- move => v. case => l F e0. case => l' F' e1. case => l'' F''. simpl. exists (l ++ map (fun x => x.-1) l' ++ map (fun x => x.-1) l'').
  rewrite (free_varVW F) ; first rewrite (free_varEW F') ; first rewrite (free_varEW F'') ; first by [].
  + case ; first by rewrite in_cons ; rewrite eq_refl.
    move => i I. rewrite in_cons. simpl. rewrite map_cat. rewrite map_cat. rewrite mem_cat. simpl.
    rewrite mem_cat. rewrite map_map. rewrite map_map.
    clear F F' F''. have T:(i.+1 \in map (fun x : nat => x.-1.+1) l'').
    elim: l'' I ; first by []. simpl. case.
    + simpl => s IH. rewrite in_cons. simpl. move => A. rewrite in_cons. rewrite (IH A). by rewrite orbT.
    + simpl. move => j s IH. rewrite in_cons. rewrite in_cons. move => X.
      destruct (orP X) as [A | A] ; first by rewrite A. rewrite (IH A). by rewrite orbT.
    rewrite T. by case: (i.+1 \in map S l) ; rewrite orbT.
  + case ; first by rewrite in_cons ; rewrite eq_refl.
    move => i I. rewrite in_cons. simpl. rewrite map_cat. rewrite map_cat. rewrite mem_cat. do 2 rewrite map_map.
    clear F F'' F'. have T:(i.+1 \in map (fun x : nat => x.-1.+1) l').
    elim: l' I ; first by []. simpl. case.
    + simpl => s IH. rewrite in_cons. simpl. move => A. rewrite in_cons. rewrite (IH A). by rewrite orbT.
    + simpl. move => j s IH. rewrite in_cons. rewrite in_cons. move => X.
      destruct (orP X) as [A | A] ; first by rewrite A. rewrite (IH A). by rewrite orbT. rewrite mem_cat.
    rewrite T. by rewrite orbT.
  + move => i A. rewrite mem_cat. by rewrite A.
Qed.

Lemma subst_eq n:
  (forall (v:Value n) s s' l, free_varV v l -> (forall i, i \in l -> nth UNIT s i = nth UNIT s' i) -> substV s v = substV s' v) /\
  (forall (e:Exp n) s s' l, free_varE e l  -> (forall i, i \in l -> nth UNIT s i = nth UNIT s' i) -> substE s e = substE s' e).
apply ExpValue_ind => n.
- move => i s s' l F X. simpl. apply X. by apply F.
- by [].
- by [].
- move => e IH s s' l F X. simpl. f_equal. apply (IH _ _ _ F). move => i I.
  case_eq (i < size s) => X'.
  + specialize (X i I). have e':=f_equal ((@vtsubst _ (drop 1 (idsub 0 n.+1)) n)) X.
    rewrite <- (nth_map _ UNIT _ X') in e'. rewrite e'. clear.
    case_eq (i < size s') => C ; first by rewrite (nth_map UNIT _ _ C).
    rewrite ltnNge in C. have e:=negbFE C. clear C. rewrite (nth_default UNIT e).
    by rewrite (nth_default UNIT) ; last by rewrite size_map.
  + rewrite ltnNge in X'. have E:=negbFE X'. rewrite (nth_default UNIT) ; last by rewrite size_map.
    case_eq (i < size s') => Y.
    * rewrite (nth_map UNIT _ _ Y). specialize (X i I). rewrite (nth_default UNIT E) in X. by rewrite <- X.
    * rewrite ltnNge in Y. have YY:=negbFE Y. clear Y. by rewrite (nth_default UNIT) ; last rewrite size_map.
- move => t e IH s s' l F X. simpl. f_equal. simpl in F. apply (IH _ _ (O::map S l) F). case ; first by [].
  move => i. rewrite in_cons. simpl. move => I. rewrite (mem_map succn_inj) in I. specialize (X i I).
  case_eq (i < size s) => E.
  + rewrite (nth_map UNIT _ _ E). rewrite X. case_eq (i < size s') => E' ; first by rewrite (nth_map UNIT _ _ E').
    rewrite ltnNge in E'. have ee:=negbFE E'. rewrite (nth_default UNIT ee).
    by rewrite (nth_default UNIT) ; last by rewrite size_map.
  + rewrite ltnNge in E. have E':=negbFE E. rewrite (nth_default UNIT) ; last by rewrite size_map.
    rewrite (nth_default UNIT E') in X. case_eq (i < size s') => Y ; first by rewrite (nth_map UNIT _ _ Y) ; rewrite <- X.
    rewrite ltnNge in Y. have YY:=negbFE Y. by rewrite (nth_default UNIT) ; last by rewrite size_map.
(*- move => t0 t e IH s s' X. simpl. f_equal. apply IH. case ; first by []. case ; first by [].
  move => i. simpl. specialize (X i).
  case_eq (i < size s) => E.
  + rewrite (nth_map UNIT _ _ E). rewrite X. case_eq (i < size s') => E' ; first by rewrite (nth_map UNIT _ _ E').
    rewrite ltnNge in E'. have ee:=negbFE E'. rewrite (nth_default UNIT ee).
    by rewrite (nth_default UNIT) ; last by rewrite size_map.
  + rewrite ltnNge in E. have E':=negbFE E. rewrite (nth_default UNIT) ; last by rewrite size_map.
    rewrite (nth_default UNIT E') in X. case_eq (i < size s') => Y ; first by rewrite (nth_map UNIT _ _ Y) ; rewrite <- X.
    rewrite ltnNge in Y. have YY:=negbFE Y. by rewrite (nth_default UNIT) ; last by rewrite size_map.*)
- by [].
- move => v0 IH0 v1 IH1 s s' l F X. simpl. simpl in F. rewrite (IH0 _ _ l (proj1 (andP F)) X). by rewrite (IH1 _ _ _ (proj2 (andP F)) X).
- move => t v IH s s' l F X. simpl. by rewrite (IH _ _ _ F X).
- move => t v IH s s' l F X. simpl. by rewrite (IH _ _ _ F X).
- move => t v IH s s' l F X. simpl. by rewrite (IH _ _ _ F X).
- move => v IH s s' l F X. simpl. by rewrite (IH _ _ _ F X).
- move => v IH s s' l F X. simpl. by rewrite (IH _ _ _ F X).
- move => v IH s s' l F X. simpl. by rewrite (IH _ _ _ F X).
- move => op v IH s s' l F X. simpl. by rewrite (IH _ _ _ F X).
- move => v IH s s' l F X. simpl. by rewrite (IH _ _ _ F X).
- move => v IH s s' l F X. simpl. by rewrite (IH _ _ _ F X).
- move => v IH s s' l F X. simpl. by rewrite (IH _ _ _ F X).
- move => v0 IH0 v1 IH1 s s' l F X. simpl. simpl in F. rewrite (IH0 _ _ l (proj1 (andP F)) X). by rewrite (IH1 _ _ _ (proj2 (andP F)) X).
- move => e0 IH0 e1 IH1 s s' l F X. simpl. rewrite (IH0 _ _ _ (proj1 (andP F)) X). f_equal.
  apply (IH1 _ _ _ (proj2 (andP F))). case ; first by [].
  move => i. simpl. rewrite in_cons. simpl. rewrite (mem_map succn_inj). move => I. specialize (X i I).
  case_eq (i < size s) => E.
  + rewrite (nth_map UNIT _ _ E). rewrite X. case_eq (i < size s') => E' ; first by rewrite (nth_map UNIT _ _ E').
    rewrite ltnNge in E'. have ee:=negbFE E'. rewrite (nth_default UNIT ee).
    by rewrite (nth_default UNIT) ; last by rewrite size_map.
  + rewrite ltnNge in E. have E':=negbFE E. rewrite (nth_default UNIT) ; last by rewrite size_map.
    rewrite (nth_default UNIT E') in X. case_eq (i < size s') => Y ; first by rewrite (nth_map UNIT _ _ Y) ; rewrite <- X.
    rewrite ltnNge in Y. have YY:=negbFE Y. by rewrite (nth_default UNIT) ; last by rewrite size_map.
- move => v0 IH0 v1 IH1 s s' l F X. simpl. simpl in F. rewrite (IH0 _ _ l (proj1 (andP F)) X). by rewrite (IH1 _ _ _ (proj2 (andP F)) X).
- move => v IH t s s' l F X. simpl. by rewrite (IH _ _ _ F X).
- move => v IHv e0 IH0 e1 IH1 s s' l F X. simpl. rewrite (IHv _ _ _ (proj1 (andP (proj1 (andP F)))) X).
  f_equal. apply (IH0 _ _ _ (proj2 (andP (proj1 (andP F))))). case ; first by [].
  move => i. rewrite in_cons. simpl. rewrite (mem_map succn_inj). move => I. specialize (X i I).
  case_eq (i < size s) => E.
  + rewrite (nth_map UNIT _ _ E). rewrite X. case_eq (i < size s') => E' ; first by rewrite (nth_map UNIT _ _ E').
    rewrite ltnNge in E'. have ee:=negbFE E'. rewrite (nth_default UNIT ee).
    by rewrite (nth_default UNIT) ; last by rewrite size_map.
  + rewrite ltnNge in E. have E':=negbFE E. rewrite (nth_default UNIT) ; last by rewrite size_map.
    rewrite (nth_default UNIT E') in X. case_eq (i < size s') => Y ; first by rewrite (nth_map UNIT _ _ Y) ; rewrite <- X.
    rewrite ltnNge in Y. have YY:=negbFE Y. by rewrite (nth_default UNIT) ; last by rewrite size_map.
  apply (IH1 _ _ _ (proj2(andP F))). case ; first by [].
  move => i. rewrite in_cons. simpl. rewrite (mem_map succn_inj). move => I. specialize (X i I).
  case_eq (i < size s) => E.
  + rewrite (nth_map UNIT _ _ E). rewrite X. case_eq (i < size s') => E' ; first by rewrite (nth_map UNIT _ _ E').
    rewrite ltnNge in E'. have ee:=negbFE E'. rewrite (nth_default UNIT ee).
    by rewrite (nth_default UNIT) ; last by rewrite size_map.
  + rewrite ltnNge in E. have E':=negbFE E. rewrite (nth_default UNIT) ; last by rewrite size_map.
    rewrite (nth_default UNIT E') in X. case_eq (i < size s') => Y ; first by rewrite (nth_map UNIT _ _ Y) ; rewrite <- X.
    rewrite ltnNge in Y. have YY:=negbFE Y. by rewrite (nth_default UNIT) ; last by rewrite size_map.
Qed.

Definition substV_eq n := proj1 (@subst_eq n).
Definition substE_eq n := proj2 (@subst_eq n).

Lemma vsubst_ext n:
  (forall (v:Value n) m (s s':seq (Ty m)), (forall i, i < n -> nth Unit s i = nth Unit s' i) -> vtsubst s v = vtsubst s' v) /\
  (forall (e:Exp n) m (s s':seq (Ty m)), (forall i, i < n -> nth Unit s i = nth Unit s' i) -> etsubst s e = etsubst s' e).
apply ExpValue_ind => n.
- by [].
- by [].
- by [].
- move => e IH m s s' X. simpl. apply f_equal. apply IH. case ; first by []. simpl. move => i L. specialize (X i L).
  case_eq (i < size s) => E.
  + rewrite (nth_map Unit _ _ E). rewrite X. case_eq (i < size s') => E' ; first by rewrite (nth_map Unit _ _ E').
    rewrite ltnNge in E'. have X':=negbFE E'. rewrite (nth_default Unit X').
    rewrite (nth_default Unit) ; last by rewrite size_map. by rewrite tshiftL_unit.
  + rewrite ltnNge in E. have E':=negbFE E. clear E. rewrite (nth_default Unit) ; last by rewrite size_map.
    rewrite (nth_default Unit E') in X. case_eq (i < size s') => E ; first by
      rewrite (nth_map Unit _ _ E) ; rewrite <- X ; rewrite tshiftL_unit.
    rewrite ltnNge in E. have X':=negbFE E. clear E. by rewrite (nth_default Unit) ; last by rewrite size_map.
- move => t e IH m s s' X. simpl. rewrite (IH _ _ _ X). by rewrite (tsubst_ext _ X).
(*- move => t0 t e IH m s s' X. simpl. rewrite (IH _ _ _ X). rewrite (tsubst_ext _ X). by rewrite (tsubst_ext _ X).*)
- by [].
- move => v0 IH0 v1 IH1 m s s' X. simpl. rewrite (IH0 _ _ _ X). by rewrite (IH1 _ _ _ X).
- move => t v IH m s s' X. simpl. rewrite (tsubst_ext _ X). by rewrite (IH _ _ _ X).
- move => t v IH m s s' X. simpl. rewrite (tsubst_ext _ X). by rewrite (IH _ _ _ X).
- move => t v IH m s s' X. simpl. rewrite (IH _ _ _ X). f_equal.
  apply tsubst_ext. case ; first by []. move => i L. simpl. specialize (X i L). case_eq (i < size s) => E.
  + rewrite (nth_map Unit _ _ E). rewrite X. clear. case_eq (i < size s') => E ; first by rewrite (nth_map Unit _ _ E).
    rewrite ltnNge in E. have E':=negbFE E. rewrite (nth_default Unit E').
    rewrite (nth_default Unit) ; last by rewrite size_map. by rewrite tshiftL_unit.
  + rewrite ltnNge in E. have E':=negbFE E. rewrite (nth_default Unit) ; last by rewrite size_map.
    rewrite (nth_default Unit E') in X.
    case_eq (i < size s') => A ; first by rewrite (nth_map Unit _ _ A) ; rewrite <- X ; rewrite tshiftL_unit.
    rewrite ltnNge in A. have A':=negbFE A. by rewrite (nth_default Unit) ; last by rewrite size_map.
- move => v IH m s s' X. simpl. by rewrite (IH _ _ _ X).
- move => v IH m s s' X. simpl. by rewrite (IH _ _ _ X).
- move => v IH m s s' X. simpl. by rewrite (IH _ _ _ X).
- move => op v IH m s s' X. simpl. by rewrite (IH _ _ _ X).
- move => v IH m s s' X. simpl. by rewrite (IH _ _ _ X).
- move => v IH m s s' X. simpl. by rewrite (IH _ _ _ X).
- move => v IH m s s' X. simpl. by rewrite (IH _ _ _ X).
- move => e0 IH0 e1 IH1 m s s' X. simpl. rewrite (IH0 _ _ _ X). by rewrite (IH1 _ _ _ X).
- move => v0 IH0 v1 IH1 m s s' X. simpl. rewrite (IH0 _ _ _ X). by rewrite (IH1 _ _ _ X).
- move => e0 IH0 e1 IH1 m s s' X. simpl. rewrite (IH0 _ _ _ X). by rewrite (IH1 _ _ _ X).
- move => v IH t m s s' X. simpl. rewrite (tsubst_ext _ X). by rewrite (IH _ _ _ X).
- move => v0 IH0 v1 IH1 v2 IH2 m s s' X. simpl. rewrite (IH0 _ _ _ X). rewrite (IH1 _ _ _ X). by rewrite (IH2 _ _ _ X).
Qed.

Definition vtsubst_ext n := proj1 (@vsubst_ext n).
Definition etsubst_ext n := proj2 (@vsubst_ext n).

Lemma xtsubst_map i :
  (forall (t:Value i) n (s:seq (Ty n)) m (s':seq (Ty m)), vtsubst s (vtsubst s' t) = vtsubst (map (@tsubst _ s _) s') t) /\
  (forall (t:Exp i) n (s:seq (Ty n)) m (s':seq (Ty m)), etsubst s (etsubst s' t) = etsubst (map (@tsubst _ s _) s') t).
apply ExpValue_ind => n.
- by [].
- by [].
- by [].
- move => e IH j s m s'. simpl. rewrite IH. f_equal. apply etsubst_ext.
  case ; first by []. simpl. move => i L. rewrite map_map. rewrite map_map.
  case_eq (i < size s') => E.
  + rewrite (nth_map Unit _ _ E). rewrite (nth_map Unit _ _ E).
    rewrite <- (tsubst_shiftL' (nth Unit s' i) (s':=(TVar (n:=1+j) (i:=0) (ltn0Sn j) :: map (@tshiftL 0 1 _) s))) ;
      [by [] | by rewrite take0 | by simpl ; rewrite map_drop].
  + rewrite ltnNge in E. have E':=negbFE E. clear E. rewrite (nth_default Unit) ; last by rewrite size_map.
    by rewrite (nth_default Unit) ; last by rewrite size_map.
- move => t e IH j s m s'. simpl. rewrite IH. clear. by rewrite tsubst_map.
(*- move => t0 t1 e IH j s m s'. simpl. rewrite IH. clear. by do 2 rewrite tsubst_map.*)
- by [].
- move => v0 IH0 v1 IH1 k s m s'. simpl. rewrite IH0. by rewrite IH1.
- move => t v IH k s m s'. simpl. rewrite tsubst_map. by rewrite IH.
- move => t v IH k s m s'. simpl. rewrite tsubst_map. by rewrite IH.
- move => t e IH j s m s'. simpl. rewrite IH. rewrite tsubst_map. f_equal. apply tsubst_ext.
  case ; first by []. simpl. move => i L. rewrite map_map. rewrite map_map.
  case_eq (i < size s') => E.
  + rewrite (nth_map Unit _ _ E). rewrite (nth_map Unit _ _ E).
    by rewrite <- (tsubst_shiftL' (nth Unit s' i) (s':=(TVar (n:=1+j) (i:=0) (ltn0Sn j) :: map (@tshiftL 0 1 _) s))) ;
      [by [] | by rewrite take0 | by simpl ; rewrite map_drop].
  + rewrite ltnNge in E. have E':=negbFE E. clear E. rewrite (nth_default Unit) ; last by rewrite size_map.
    by rewrite (nth_default Unit) ; last by rewrite size_map.
- move => v IH k s m s'. simpl. by rewrite IH.
- move => v IH k s m s'. simpl. by rewrite IH.
- move => v IH k s m s'. simpl. by rewrite IH.
- move => op v IH k s m s'. simpl. by rewrite IH.
- move => v IH k s m s'. simpl. by rewrite IH.
- move => v IH k s m s'. simpl. by rewrite IH.
- move => v IH k s m s'. simpl. by rewrite IH.
- move => e0 IH0 e1 IH1 j s m s'. simpl. rewrite IH0. by rewrite IH1.
- move => e0 IH0 e1 IH1 j s m s'. simpl. rewrite IH0. by rewrite IH1.
- move => v0 IH0 v1 IH1 k s m s'. simpl. rewrite IH0. by rewrite IH1.
- move => v IH t k s m s'. simpl. rewrite tsubst_map. by rewrite IH.
- move => v0 IH0 v1 IH1 v2 IH2 k s m s'. simpl. rewrite IH0. rewrite IH2. by rewrite IH1.
Qed.

Definition vtsubst_map i := proj1 (@xtsubst_map i).
Definition etsubst_map i := proj2 (@xtsubst_map i).

Lemma subst_tsubst n : 
  (forall (v:Value n) s m (s':seq (Ty m)), substV (map (@vtsubst _ s' _) s) (vtsubst s' v) = vtsubst s' (substV s v)) /\
  (forall (e:Exp n) s m (s':seq (Ty m)), substE (map (@vtsubst _ s' _) s) (etsubst s' e) = etsubst s' (substE s e)).
apply ExpValue_ind => n.
- move => i s m s'. simpl. case_eq (i < size s) => E ; first by rewrite (nth_map UNIT _ _ E).
  rewrite ltnNge in E. have E':=negbFE E. clear E. rewrite (nth_default UNIT) ; last by rewrite size_map.
  by rewrite (nth_default UNIT E').
- by [].
- by [].
- move => e IH s m s'. simpl. rewrite <- IH. f_equal. clear. rewrite map_map. rewrite map_map.
  case: (proj2 (@free_var_exists _) (etsubst (TVar (ltn0Sn m) :: map (@tshiftL 0 1 _) s') e)) => l F.
  apply (substE_eq F). move => i I. case_eq (i < size s) => E.
  + rewrite (nth_map UNIT _ _ E). rewrite (nth_map UNIT _ _ E). do 2 rewrite vtsubst_map.
    apply vtsubst_ext. move => j L. case_eq (j < size s') => X.
    - rewrite (nth_map Unit _ _ X). rewrite (nth_map Unit) ; last by rewrite size_drop; rewrite (size_idsub 0 n.+1) ; rewrite subn1.
      rewrite (nth_drop). unfold addn. unfold addn_rec. rewrite (@nth_idsub n.+1 0 j.+1 L). simpl.
      clear I F e s E. rewrite (nth_map Unit _ _ X). have a:= tsubst_idsubL (nth Unit s' j).
      have b:=a 1 0 (drop 1 (idsub 0 m.+1)). clear a. apply b ; clear b ; first by [].
      move => k _. by rewrite nth_drop.
    - rewrite map_drop. rewrite nth_drop. rewrite ltnNge in X. have XX:=negbFE X. clear X.
      rewrite nth_default ; last by rewrite size_map.
      rewrite (nth_map Unit) ; last by rewrite (size_idsub 0 n.+1) ; apply L. rewrite (@nth_idsub n.+1 0 (1+j) L).
      simpl. by rewrite (nth_default Unit) ; last by rewrite size_map.
  + rewrite ltnNge in E. clear l F I. have l:=negbFE E. clear E. rewrite (nth_default UNIT) ; last by rewrite size_map.
    by rewrite (nth_default UNIT) ; last by rewrite size_map.
- move => t e IH s m s'. simpl. f_equal. rewrite <- IH. clear IH. rewrite map_map. simpl. rewrite map_map.
  case: (proj2 (@free_var_exists _) (etsubst s' e)) => l F.
  apply (substE_eq F). case ; first by []. simpl. move => j _. clear l F. case_eq (j < size s) => l.
  + rewrite (nth_map UNIT _ _ l). rewrite (nth_map UNIT _ _ l). by rewrite vtsubst_shiftV.
  + rewrite ltnNge in l. have ll:=negbFE l. clear l. rewrite (nth_default UNIT) ; last by rewrite size_map.
    by rewrite (nth_default UNIT) ; last by rewrite size_map.
(*- move => t t' e IH s m s'. simpl. f_equal. rewrite <- IH. clear IH. rewrite map_map. simpl. rewrite map_map.
  apply substE_eq. case ; first by []. simpl. case ; first by []. simpl. move => j. case_eq (j < size s) => l.
  + rewrite (nth_map UNIT _ _ l). rewrite (nth_map UNIT _ _ l). by rewrite vtsubst_shiftV.
  + rewrite ltnNge in l. have ll:=negbFE l. clear l. rewrite (nth_default UNIT) ; last by rewrite size_map.
    by rewrite (nth_default UNIT) ; last by rewrite size_map.*)
- by [].
- move => v0 IH0 v1 IH1 s m s'. simpl. rewrite (IH0 s _ s'). by rewrite IH1.
- move => t v0 IH0 s m s'. simpl. by rewrite (IH0 s _ s').
- move => t v0 IH0 s m s'. simpl. by rewrite (IH0 s _ s').
- move => t v0 IH0 s m s'. simpl. by rewrite (IH0 s _ s').
- move => v0 IH0 s m s'. simpl. by rewrite (IH0 s _ s').
- move => v0 IH0 s m s'. simpl. by rewrite (IH0 s _ s').
- move => v0 IH0 s m s'. simpl. by rewrite (IH0 s _ s').
- move => op v0 IH0 s m s'. simpl. by rewrite (IH0 s _ s').
- move => v0 IH0 s m s'. simpl. by rewrite (IH0 s _ s').
- move => v0 IH0 s m s'. simpl. by rewrite (IH0 s _ s').
- move => v0 IH0 s m s'. simpl. by rewrite (IH0 s _ s').
- move => v0 IH0 v1 IH1 s m s'. simpl. rewrite (IH0 s _ s'). by rewrite IH1.
- move => e0 IH0 e1 IH1 s m s'. simpl. rewrite (IH0 _ _ _). f_equal. rewrite <- IH1. clear IH1 IH0.
  rewrite map_map. simpl. rewrite map_map.
  case: (proj2 (@free_var_exists _) (etsubst s' e1)) => l F.
  apply (substE_eq F). case ; first by []. simpl. move => j _. clear l F. case_eq (j < size s) => l.
  + rewrite (nth_map UNIT _ _ l). rewrite (nth_map UNIT _ _ l). by rewrite vtsubst_shiftV.
  + rewrite ltnNge in l. have ll:=negbFE l. clear l. rewrite (nth_default UNIT) ; last by rewrite size_map.
    by rewrite (nth_default UNIT) ; last by rewrite size_map.
- move => v0 IH0 v1 IH1 s m s'. simpl. rewrite (IH0 s _ s'). by rewrite IH1.
- move => v0 IH0 t s m s'. simpl. by rewrite (IH0 s _ s').
- move => e0 IH0 e1 IH1 e2 IH2 s m s'. simpl. rewrite (IH0 _ _ _). f_equal.
  + rewrite <- IH1. clear IH1 IH0.
    rewrite map_map. simpl. rewrite map_map.
    case: (proj2 (@free_var_exists _) (etsubst s' e1)) => l F.
    apply (substE_eq F). case ; first by []. simpl. move => j _. clear l F. case_eq (j < size s) => l.
    * rewrite (nth_map UNIT _ _ l). rewrite (nth_map UNIT _ _ l). by rewrite vtsubst_shiftV.
    * rewrite ltnNge in l. have ll:=negbFE l. clear l. rewrite (nth_default UNIT) ; last by rewrite size_map.
      by rewrite (nth_default UNIT) ; last by rewrite size_map.
  + rewrite <- IH2. clear IH1 IH0 IH2.
    rewrite map_map. simpl. rewrite map_map.
    case: (proj2 (@free_var_exists _) (etsubst s' e2)) => l F.
    apply (substE_eq F). case ; first by []. simpl. move => j _. clear l F. case_eq (j < size s) => l.
    * rewrite (nth_map UNIT _ _ l). rewrite (nth_map UNIT _ _ l). by rewrite vtsubst_shiftV.
    * rewrite ltnNge in l. have ll:=negbFE l. clear l. rewrite (nth_default UNIT) ; last by rewrite size_map.
      by rewrite (nth_default UNIT) ; last by rewrite size_map.
Qed.

Definition vtsubst_tsubst n := proj1 (subst_tsubst n).
Definition etsubst_tsubst n := proj2 (subst_tsubst n).

Lemma subst_map n :
  (forall (t:Value n) (s:seq (Value n)) (s':seq (Value n)), substV s (substV s' t) = substV (map (substV s) s') t) /\
  (forall (t:Exp n) (s:seq (Value n)) (s':seq (Value n)), substE s (substE s' t) = substE (map (substV s) s') t).
apply ExpValue_ind => n.
- move => i s s'. simpl. case_eq (i < size s') => E ; first by rewrite (nth_map UNIT _ _ E).
  rewrite ltnNge in E. have E':=negbFE E. clear E. rewrite (nth_default UNIT E').
  by rewrite (nth_default UNIT) ; last by rewrite size_map.
- by [].
- by [].
- move => e IH s s'. simpl. rewrite IH. rewrite map_map. simpl. f_equal. rewrite map_map.
  case: (proj2 (@free_var_exists _) e) => l F.
  apply (substE_eq F). move => i _. clear. case_eq (i < size s') => E.
  + rewrite (nth_map UNIT _ _ E). rewrite (nth_map UNIT _ _ E). by rewrite vtsubst_tsubst.
  + rewrite ltnNge in E. have e:=negbFE E. clear E. rewrite (nth_default UNIT) ; last by rewrite size_map.
    by rewrite (nth_default UNIT) ; last by rewrite size_map.
- move => t e IH s s'. simpl. f_equal. rewrite IH. clear IH. rewrite map_map. simpl. rewrite map_map.
  case: (proj2 (@free_var_exists _) e) => l F.
  apply (substE_eq F). case ; first by []. simpl. move => j _. clear. case_eq (j < size s') => E.
  + rewrite (nth_map UNIT _ _ E). rewrite (nth_map UNIT _ _ E). apply substV_shiftV ; first by rewrite take0.
    rewrite drop0. simpl. by rewrite drop0.
  + rewrite ltnNge in E. have E':=negbFE E. clear E. rewrite (nth_default UNIT) ; last by rewrite size_map.
    by rewrite (nth_default UNIT) ; last by rewrite size_map.
(*- move => t t' e IH s s'. simpl. f_equal. rewrite IH. clear IH. rewrite map_map. simpl. rewrite map_map.
  apply substE_eq. case ; first by []. simpl. case ; first by []. simpl. move => j. case_eq (j < size s') => E.
  + rewrite (nth_map UNIT _ _ E). rewrite (nth_map UNIT _ _ E). apply substV_shiftV ; first by rewrite take0.
    rewrite drop0. simpl. by rewrite drop0.
  + rewrite ltnNge in E. have E':=negbFE E. clear E. rewrite (nth_default UNIT) ; last by rewrite size_map.
    by rewrite (nth_default UNIT) ; last by rewrite size_map.*)
- by [].
- move => v0 IH0 v1 IH1 s s'. simpl. rewrite IH0. by rewrite IH1.
- move => t v IH s s'. simpl. by rewrite IH.
- move => t v IH s s'. simpl. by rewrite IH.
- move => t v IH s s'. simpl. by rewrite IH.
- move => v IH s s'. simpl. by rewrite IH.
- move => v IH s s'. simpl. by rewrite IH.
- move => v IH s s'. simpl. by rewrite IH.
- move => op v IH s s'. simpl. by rewrite IH.
- move => v IH s s'. simpl. by rewrite IH.
- move => v IH s s'. simpl. by rewrite IH.
- move => v IH s s'. simpl. by rewrite IH.
- move => v0 IH0 v1 IH1 s s'. simpl. rewrite IH0. by rewrite IH1.
- move => e0 IH0 e1 IH1 s s'. simpl. rewrite IH0. f_equal. rewrite IH1. clear IH0 IH1. rewrite map_map. simpl. rewrite map_map.
  case: (proj2 (@free_var_exists _) e1) => l F.
  apply (substE_eq F). case ; first by []. simpl. move => j _. clear. case_eq (j < size s') => E.
  + rewrite (nth_map UNIT _ _ E). rewrite (nth_map UNIT _ _ E). apply substV_shiftV ; first by rewrite take0.
    rewrite drop0. simpl. by rewrite drop0.
  + rewrite ltnNge in E. have E':=negbFE E. clear E. rewrite (nth_default UNIT) ; last by rewrite size_map.
    by rewrite (nth_default UNIT) ; last by rewrite size_map.
- move => v0 IH0 v1 IH1 s s'. simpl. rewrite IH0. by rewrite IH1.
- move => v IH t s s'. simpl. by rewrite IH.
- move => e0 IH0 e1 IH1 e2 IH2 s s'. simpl. rewrite IH0. f_equal.
  + rewrite IH1. clear IH0 IH1. rewrite map_map. simpl. rewrite map_map.
    case: (proj2 (@free_var_exists _) e1) => l F.
    apply (substE_eq F). case ; first by []. simpl. move => j _. clear. case_eq (j < size s') => E.
    * rewrite (nth_map UNIT _ _ E). rewrite (nth_map UNIT _ _ E). apply substV_shiftV ; first by rewrite take0.
      rewrite drop0. simpl. by rewrite drop0.
    * rewrite ltnNge in E. have E':=negbFE E. clear E. rewrite (nth_default UNIT) ; last by rewrite size_map.
      by rewrite (nth_default UNIT) ; last by rewrite size_map.
  + rewrite IH2. clear IH0 IH1. rewrite map_map. simpl. rewrite map_map.
    case: (proj2 (@free_var_exists _) e2) => l F.
    apply (substE_eq F). case ; first by []. simpl. move => j _. clear. case_eq (j < size s') => E.
    * rewrite (nth_map UNIT _ _ E). rewrite (nth_map UNIT _ _ E). apply substV_shiftV ; first by rewrite take0.
      rewrite drop0. simpl. by rewrite drop0.
    * rewrite ltnNge in E. have E':=negbFE E. clear E. rewrite (nth_default UNIT) ; last by rewrite size_map.
      by rewrite (nth_default UNIT) ; last by rewrite size_map.
Qed.

Definition substV_map n := proj1 (subst_map n).
Definition substE_map n := proj2 (subst_map n).

Lemma def_on_dom X Y (f:FinDom X Y) l : isSome (f l) = (l \in dom f).
move => X Y f l. case: f. unfold findom_f. unfold dom. simpl. elim ; first by [].
case => e0 e1 s IH PP. simpl. case_eq (l == e0) => e ; rewrite in_cons; first by rewrite e.
- rewrite e. simpl. simpl @map in PP. rewrite sorted_cons in PP. simpl in PP.
  rewrite (proj2 (andP (proj1 (andP PP)))) in IH. rewrite (proj2 (andP (proj2 (andP PP)))) in IH.
  by apply IH.
Qed.

Lemma findom_leq_def T (T':eqType) (S S':FinDom T T') l : findom_leq S S' -> l \in dom S -> S l = S' l.
move => T T' S S' l L I. case: S L I. unfold dom. unfold findom_leq. unfold findom_f. simpl. case: S'. unfold dom. simpl.
move => s' P' s PP. move => X Y. have a:=elimT (@allP _ _ (map (@fst _ _ ) s)) X _ Y. by apply (eqP a).
Qed.

Lemma findom_leq_defI T (T':eqType) (S S':FinDom T T') : (forall l, l \in dom S -> S l = S' l) -> findom_leq S S'.
move => T T' S S' I. unfold findom_leq. apply (introT (@allP _ _ (dom S))). move => x E.
specialize (I _ E). by rewrite I.
Qed.

Lemma dom_post_compt T T' (x:FinDom T T') T'' (f:T' -> T'') : dom (post_compt f x) = dom x.
move => T T'. case. unfold dom. simpl. move => s PP T'' f. rewrite map_pmap. simpl. clear PP f T''.
elim: s ; first by []. move => t s IH. simpl. by rewrite IH.
Qed.

Lemma Lweakening_deriv (l:nat) i E S t :
   (forall v, i |- E | S |v- v ::: t -> forall S', findom_leq S S' -> i |- E | S' |v- v ::: t) *
   (forall e, i |- E | S |e- e ::: t -> forall S', findom_leq S S' -> i |- E | S' |e- e ::: t).
move => l. apply (@Typing_rect) => i E S t.
- by move => m e S' X ; apply TvVAR.
- move => t0 l0 e e' S' C. rewrite e'. clear e'. apply: (TvLOC _ _ (refl_equal _)).
  rewrite <- (findom_leq_def C) ; first by []. have a:=def_on_dom S l0. rewrite e in a. simpl in a.
  by rewrite (sym_eq a).
- move => n e C L. by apply TvINT.
- move => e t' e'. rewrite e' ; clear t e'. move => D IH S' L. apply (TvTLAM (refl_equal _)).
  apply IH. apply findom_leq_defI. move => l0 I. rewrite dom_post_compt in I.
  have X:=findom_leq_def L I. rewrite post_comp_simpl. rewrite X. by rewrite post_comp_simpl. 
- move => b t0 t1 e d IH C L. specialize (IH C L). by apply: (TvLAMBDA _ IH).
- move => e C L. by apply TvUNIT.
- move => t0 t1 v0 v1 e d0 IH0 d1 IH1 C L. specialize (IH0 C L). specialize (IH1 C L). by apply: (TvP e).
- move => t0 t1 v d IH e C L. specialize (IH C L). by apply: (TvINL _ e).
- move => t0 t1 v d IH e C L. specialize (IH C L). by apply: (TvINR _ e).
- move => t0 v d IH e C L. specialize (IH C L). by apply TvFOLD.
- move => v d IH C L. specialize (IH C L). by apply TeVAL.
- move => e0 e1 t0 d0 IH0 d1 IH1 C L. specialize (IH0 C L). specialize (IH1 C L). by apply (TeLET IH0 IH1).
- move => t0 v d IH C L. specialize (IH C L). apply (TvFST IH).
- move => t0 v d IH C L. specialize (IH C L). apply (TvSND IH).
- move => op v e d IH C L. specialize (IH C L). apply (TvOP op e IH).
- move => t0 v d IH e C L. specialize (IH C L). by apply (TvUNFOLD IH).
- move => v t0 d IH e C L. specialize (IH C L). by apply (TvREF IH).
- move => v d IH C L. specialize (IH C L). by apply (TvBANG IH).
- move => v0 v1 t0 d0 IH0 d1 IH1 e C L. specialize (IH0 C L). specialize (IH1 C L). by apply (TvASSIGN IH0 IH1).
- move => v0 v1 t0 d0 IH0 d1 IH1 C L. specialize (IH0 C L). specialize (IH1 C L). by apply (TeAPP IH0 IH1).
- move => v0 v1 t0 d0 IH0 e C L. specialize (IH0 C L). by apply (TeTAPP IH0).
- move => v0 e0 e1 t0 t1 d0 IH0 d1 IH1 d2 IH2 C L. specialize (IH0 C L). specialize (IH1 C L). specialize (IH2 C L).
  by apply (TeCASE IH0 IH1 IH2).
Qed.

Definition LweakV i l E S t := fst (@Lweakening_deriv i l E S t).
Definition LweakE i l E S t := snd (@Lweakening_deriv i l E S t).

Lemma idsub_exp n : TVar (ltn0Sn (0 + n)) :: map (@tshiftL 0 1 _) (idsub 0 n) = idsub 0 n.+1.
move => n. by apply @idsubr_shiftL1.
Qed.

Lemma tsubst_idX n : (forall (v:Value n), vtsubst (idsub 0 n) v = v) /\ (forall e, etsubst (idsub 0 n) e = e).
apply ExpValue_ind.
- by [].
- by [].
- by [].
- simpl. move => n e IH. rewrite idsub_exp. by rewrite IH.
- simpl. move => n t0 t1 IH. rewrite IH. by rewrite tsubst_id.
- by [].
- move => n v0 IH0 v1 IH1. simpl. rewrite IH0. by rewrite IH1.
- move => n t v IH. simpl. rewrite tsubst_id. by rewrite IH.
- move => n t v IH. simpl. rewrite tsubst_id. by rewrite IH.
- move => n t v IH. simpl. rewrite IH. rewrite idsub_exp. by rewrite tsubst_id.
- move => n v IH. simpl. by rewrite IH.
- move => n v IH. simpl. by rewrite IH.
- move => n v IH. simpl. by rewrite IH.
- move => n op v IH. simpl. by rewrite IH.
- move => n v IH. simpl. by rewrite IH.
- move => n v IH. simpl. by rewrite IH.
- move => n v IH. simpl. by rewrite IH.
- move => n v0 IH0 v1 IH1. simpl. rewrite IH0. by rewrite IH1.
- move => n e0 IH0 e1 IH1. simpl. rewrite IH0. by rewrite IH1.
- move => n v0 IH0 v1 IH1. simpl. rewrite IH0. by rewrite IH1.
- move => n v IH t. simpl. rewrite IH. by rewrite tsubst_id.
- move => n v IHv e0 IH0 v1 IH1. simpl. rewrite IHv. rewrite IH0. by rewrite IH1.
Qed.

Definition vtsubst_id n := proj1 (@tsubst_idX n).
Definition etsubst_id n := proj2 (@tsubst_idX n).

Lemma substX_shiftW i n :
 (forall (x:Value n) k (s:seq (Value n)) s', 
     take k s = take k s' -> drop (k+i) s = drop k s' -> substV s (shiftV k i x) = substV s' x) /\
 (forall (x:Exp n) k (s:seq (Value n)) s', 
     take k s = take k s' -> drop (k+i) s = drop k s' -> substE s (shiftE k i x) = substE s' x).
move => i. apply ExpValue_ind.
- move => j n k s s' X Y. simpl. case_eq (n < k) => E.
  + simpl. rewrite <- (nth_take UNIT E s). rewrite <- (nth_take UNIT E s'). by rewrite X.
  + simpl. rewrite ltnNge in E. have E':=negbFE E. clear E.
    rewrite addnC. have E:=subnK E'. rewrite <- E. rewrite (addnC _ k). rewrite addnA.
    rewrite <- (nth_drop _ UNIT s). rewrite addnC. rewrite Y. rewrite nth_drop. by rewrite (subnKC E').
- by [].
- by [].
- simpl. move => n e IH k s s' X Y. f_equal.
  specialize (IH k (map (@vtsubst _ (drop 1 (idsub 0 n.+1)) _) s) (map (@vtsubst _ (drop 1 (idsub 0 n.+1)) _) s')).
  do 2 rewrite <- map_take in IH. rewrite X in IH. do 2 rewrite <- map_drop in IH. rewrite Y in IH.
  by apply IH.
- move => n t e IH k s s' X Y. simpl. f_equal.
  specialize (IH k.+1 (VAR 0 :: map (@shiftV 0 1 _) s) (VAR 0 :: map (@shiftV 0 1 _) s')).
  simpl in IH. do 2 rewrite <- map_take in IH. do 2 rewrite <- map_drop in IH.
  rewrite X in IH. rewrite Y in IH. by apply IH.
- by [].
- move => n v0 IH0 v1 IH1 k s s' X Y. simpl. rewrite (IH0 k s s' X Y). by rewrite (IH1 k s s' X Y).
- move => n t v0 IH0 k s s' X Y. simpl. by rewrite (IH0 k s s' X Y).
- move => n t v0 IH0 k s s' X Y. simpl. by rewrite (IH0 k s s' X Y).
- move => n t v0 IH0 k s s' X Y. simpl. by rewrite (IH0 k s s' X Y).
- move => n v0 IH0 k s s' X Y. simpl. by rewrite (IH0 k s s' X Y).
- move => n v0 IH0 k s s' X Y. simpl. by rewrite (IH0 k s s' X Y).
- move => n v0 IH0 k s s' X Y. simpl. by rewrite (IH0 k s s' X Y).
- move => n t v0 IH0 k s s' X Y. simpl. by rewrite (IH0 k s s' X Y).
- move => n v0 IH0 k s s' X Y. simpl. by rewrite (IH0 k s s' X Y).
- move => n v0 IH0 k s s' X Y. simpl. by rewrite (IH0 k s s' X Y).
- move => n v0 IH0 k s s' X Y. simpl. by rewrite (IH0 k s s' X Y).
- move => n v0 IH0 v1 IH1 k s s' X Y. simpl. rewrite (IH0 k s s' X Y). by rewrite (IH1 k s s' X Y).
- move => n v0 IH0 v1 IH1 k s s' X Y. simpl. rewrite (IH0 k s s' X Y).
  specialize (IH1 k.+1 (VAR 0 :: map (@shiftV 0 1 _) s) (VAR 0 :: map (@shiftV 0 1 _) s')).
  simpl in IH1. do 2 rewrite <- map_take in IH1 ; do 2 rewrite <- map_drop in IH1.
  rewrite X in IH1. rewrite Y in IH1. by rewrite IH1.
- move => n v0 IH0 v1 IH1 k s s' X Y. simpl. rewrite (IH0 k s s' X Y). by rewrite (IH1 k s s' X Y).
- move => n v IH t k s s' X Y. simpl. by rewrite (IH k s s' X Y).
- move => n v0 IH0 v1 IH1 v2 IH2 k s s' X Y. simpl. rewrite (IH0 k s s' X Y).
  specialize (IH1 k.+1 (VAR 0 :: map (@shiftV 0 1 _) s) (VAR 0 :: map (@shiftV 0 1 _) s')).
  specialize (IH2 k.+1 (VAR 0 :: map (@shiftV 0 1 _) s) (VAR 0 :: map (@shiftV 0 1 _) s')).
  simpl in IH1, IH2. do 2 rewrite <- map_take in IH1, IH2 ; do 2 rewrite <- map_drop in IH1, IH2.
  rewrite -> X in IH1,IH2. rewrite Y in IH1. rewrite Y in IH2. by rewrite IH1 ; first by rewrite IH2.
Qed.

Definition substV_shiftW n i := proj1 (@substX_shiftW n i).
Definition substE_shiftW n i := proj2 (@substX_shiftW n i).

Fixpoint idsubvr (n i:nat) (r:seq (Value n)) : seq (Value n) :=
match i with
| O => r
| S i => idsubvr i (VAR i::r)
end.

Definition idsubv n i := @idsubvr n i nil.

Lemma idsubvr_cat n i s' s : @idsubvr n i (s' ++ s) = idsubvr i s' ++ s.
move => n. elim ; first by [].
move=> i IH s' s. simpl. specialize (IH (VAR i:: s') s). by apply IH.
Qed.

Lemma idsubvr_l n i s j x : j >= i -> nth x (@idsubvr n i s) j = nth x s (j - i).
move => n. elim. simpl. move => s j x L. by rewrite subn0.
move => i IH s j x L. simpl @idsubvr. specialize (IH (VAR i :: s) j x (leqW L)). rewrite IH. clear IH.
case: j L ; first by []. move => j L. rewrite subSS. by rewrite leq_subS ; last by apply L.
Qed.

Lemma nth_idsubvr n i j s x : j < i -> (forall j, j < size s -> nth x s j = VAR (j+i)) -> nth x (@idsubvr n i s) j = VAR j.
move => n. elim ; first by [].
move => i IH. move => j s x Lj X. simpl.
specialize (IH j (VAR i :: s)). case_eq (j == i) => E.
- rewrite (eqP E). rewrite (idsubvr_l (VAR i::s) x (leqnn i)). by rewrite subnn.
- have L:j < i. rewrite ltn_neqAle. rewrite E. simpl. by apply Lj.
  specialize (IH x L). apply IH. case; first by []. simpl. move => k Lk. specialize (X k Lk). rewrite X. rewrite addSn.
  by rewrite addnS.
Qed.

Lemma size_idsubvr n i s : size (@idsubvr n i s) = i+size s.
move => n. elim ; first by [].
move => i IH s. simpl. rewrite IH. simpl. rewrite addnS. by rewrite addSn.
Qed.

Lemma size_idsubv n i : size (@idsubv n i) = i.
move => n i.  rewrite size_idsubvr. simpl. by rewrite addn0.
Qed.

Lemma nth_idsubv n i x j : j < i -> nth x (@idsubv n i) j = VAR j.
move => n i x j L. apply (nth_idsubvr L). by [].
Qed.

Lemma nth_idsubv_l n i x j : (i <= j)%N -> nth x (idsubv n i) j = x.
move => n i x j L. rewrite idsubvr_l ; last by apply L. by case: (j - i).
Qed.


Lemma nth_error_size T (s:seq T) j t : nth_error s j = Some t -> j < size s.
move => T s j t. elim: s j ; first by [].
- move => t' s IH. case ; first by [].
move => j. simpl. move => e. by apply (IH j e).
Qed.

Lemma nth_error_idsubv n i j : j < i -> nth_error (@idsubv n i) j = Some (VAR j).
move => n i j L. rewrite nth_error_nth. have L':=size_idsubv n i. have L0:=L. rewrite <- L' in L. clear L'.
have A:=@nth_map _ UNIT _ None some j (idsubv n i) L. rewrite A. clear A. f_equal. by rewrite (nth_idsubv UNIT L0).
Qed.

Lemma seq_in_ext T (s s':seq T) : size s = size s' -> (forall i, i < size s -> nth_error s i = nth_error s' i) -> s = s'.
move => T. elim ; first by case.
- move => t e IH. case; first by [].
  move => t' s' Y X. simpl in Y. have Y':size e = size s' by auto.
  have e':= (X 0 (ltn0Sn _)). simpl in e'. case: e'. move => e'. rewrite e'. clear e'.
  specialize (IH s' Y'). have X':=fun i => (X (S i)). simpl in X'. clear X. by rewrite (IH X').
Qed.

Lemma comp_leq_anti (t:compType) (a b:t) : (leq a b) -> leq b a -> a = b.
case => T. unfold leq. simpl. case => l c A B C T'. simpl. move => a b l0 l1.
have A':=A a b. rewrite l0 in A'. rewrite l1 in A'. simpl in A'. by inversion A'.
Qed.

Lemma all_map T T' (f:T -> T') p l : all p (map f l) = all (fun x => p (f x)) l.
move => T T' f p. by elim ; [by [] | move => t s IH ; simpl ; rewrite IH].
Qed.

Lemma subst_id n :
  (forall v:Value n, forall i l, free_varV v l -> all (fun x => x < i) l -> substV (idsubv n i) v = v) /\
  (forall e:Exp n, forall i l, free_varE e l -> all (fun x => x < i) l -> substE (idsubv n i) e = e).
apply ExpValue_ind => n.
- move => j i l L F. simpl in L. have L': j < i by apply (allP F _ L). simpl. by rewrite (nth_idsubv UNIT L').
- by [].
- by [].
- move => e IH i l F L. simpl. f_equal. simpl in F. specialize (IH i _ F L).
  have ee:(map (@vtsubst _ (drop 1 (idsub 0 n.+1)) _) (idsubv n i)) = (idsubv n.+1 i).
  + apply seq_in_ext ; first by rewrite size_map ; do 2 rewrite size_idsubv.
    move => j L'. rewrite nth_error_map. simpl. rewrite size_map in L'. rewrite size_idsubv in L'.
    rewrite nth_error_idsubv ; last by apply L'. by rewrite nth_error_idsubv ; last by apply L'.
  by rewrite ee.
- move => t' e IH i l F L. simpl. f_equal. specialize (IH i.+1). simpl in F.
  specialize (IH _ F). simpl in IH. rewrite all_map in IH. specialize (IH L).
  have e':(VAR 0 :: map (@shiftV 0 1 _) (idsubv n i)) = (idsubv n i.+1). apply seq_in_ext.
    + simpl. rewrite size_map. by do 2 rewrite size_idsubv.
    + case ; first by simpl ; rewrite nth_error_idsubv.
      move => j. simpl. move => L'. rewrite nth_error_map. rewrite size_map in L'. rewrite size_idsubv in L'.
      rewrite (@nth_error_idsubv _ _ j L'). simpl. rewrite (nth_error_idsubv _ L'). rewrite addnS. by rewrite addn0.
  rewrite e'. by apply IH.
- by [].
- move => v0 IH0 v1 IH1 i l F L. simpl. simpl in F. rewrite (IH0 i _ (proj1 (andP F)) L).
  by rewrite (IH1 i _ (proj2 (andP F)) L).
- move => t v IH i l F L. simpl. simpl in F. by rewrite (IH i _ F L).
- move => t v IH i l F L. simpl. simpl in F. by rewrite (IH i _ F L).
- move => t v IH i l F L. simpl. simpl in F. by rewrite (IH i _ F L).
- move => v IH i l F L. simpl. simpl in F. by rewrite (IH i _ F L).
- move => v IH i l F L. simpl. simpl in F. by rewrite (IH i _ F L).
- move => v IH i l F L. simpl. simpl in F. by rewrite (IH i _ F L).
- move => op v IH i l F L. simpl. simpl in F. by rewrite (IH i _ F L).
- move => v IH i l F L. simpl. simpl in F. by rewrite (IH i _ F L).
- move => v IH i l F L. simpl. simpl in F. by rewrite (IH i _ F L).
- move => v IH i l F L. simpl. simpl in F. by rewrite (IH i _ F L).
- move => v0 IH0 v1 IH1 i l F L. simpl. simpl in F. rewrite (IH0 i _ (proj1 (andP F)) L).
  by rewrite (IH1 i _ (proj2 (andP F)) L).
- move => v0 IH0 v1 IH1 i l F L. simpl. simpl in F. rewrite (IH0 i _ (proj1 (andP F)) L).
  have e0:(VAR 0 :: map (@shiftV 0 1 _) (idsubv n i)) = (idsubv n i.+1). apply seq_in_ext.
    + simpl. rewrite size_map. by do 2 rewrite size_idsubv.
    + case ; first by simpl ; rewrite nth_error_idsubv.
      move => j. simpl. move => L'. rewrite nth_error_map. rewrite size_map in L'. rewrite size_idsubv in L'.
      rewrite (@nth_error_idsubv _ _ j L'). simpl. rewrite (nth_error_idsubv _ L'). rewrite addnS. by rewrite addn0.
  rewrite e0. specialize (IH1 i.+1 (O::map [eta S] l) (proj2 (andP F))). simpl in IH1. rewrite all_map in IH1.
  by rewrite (IH1 L).
- move => v0 IH0 v1 IH1 i l F L. simpl. simpl in F. rewrite (IH0 i _ (proj1 (andP F)) L).
  by rewrite (IH1 i _ (proj2 (andP F)) L).
- move => v IH t i l F L. simpl. simpl in F. by rewrite (IH i _ F L).
- move => v0 IH0 v1 IH1 v2 IH2 i l F L. simpl. simpl in F. rewrite (IH0 i _ (proj1 (andP (proj1 (andP F)))) L).
  have e0:(VAR 0 :: map (@shiftV 0 1 _) (idsubv n i)) = (idsubv n i.+1). apply seq_in_ext.
    + simpl. rewrite size_map. by do 2 rewrite size_idsubv.
    + case ; first by simpl ; rewrite nth_error_idsubv.
      move => j. simpl. move => L'. rewrite nth_error_map. rewrite size_map in L'. rewrite size_idsubv in L'.
      rewrite (@nth_error_idsubv _ _ j L'). simpl. rewrite (nth_error_idsubv _ L'). rewrite addnS. by rewrite addn0.
  rewrite e0. specialize (IH1 i.+1 (O::map [eta S] l)). specialize (IH2 i.+1 (O::map [eta S] l)). simpl in IH1,IH2.
  rewrite all_map in IH1. rewrite all_map in IH2. specialize (IH1 (proj2 (andP (proj1 (andP F)))) L).
  specialize (IH2 (proj2 (andP F)) L).  rewrite IH1. by rewrite IH2.
Qed.

Definition substV_id n := proj1 (@subst_id n).
Definition substE_id n := proj2 (@subst_id n).

Lemma substV_cid n (v:cvalue n) l : substV l v = v.
move => n v l. rewrite (substV_eq (s':=[::]) (cvalueP v)) ; last by [].
by apply (@substV_id _ _ O _ (cvalueP v)).
Qed.

Lemma substE_cid n (e:cexpression n) l : substE l e = e.
move => n e l. rewrite (substE_eq (s':=[::]) (cexpP e)) ; last by [].
by apply (@substE_id _ _ O _ (cexpP e)).
Qed.

