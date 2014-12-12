(**********************************************************************************
 * moperational.v                                                                 *
 * Formalizing Domains, Ultrametric Spaces and Semantics of Programming Languages *
 * Nick Benton, Lars Birkedal, Andrew Kennedy and Carsten Varming                 *
 * July 2010                                                                      *
 * Build with Coq 8.2pl1 plus SSREFLECT                                           *
 **********************************************************************************)

(* Operational semantics of the kitchen sink language *)

Require Import Finmap msyntax.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Definition Heap := FinDom [compType of nat] (Value O).

(*=EV *)
Inductive EV : nat -> (Exp 0) -> Heap -> Value O -> Heap -> Type :=
| EvVAL h v : EV O (VAL v) h v h
| EvFST h v0 v1 : EV O (FST (P v0 v1)) h v0 h
| EvSND h v0 v1 : EV O (SND (P v0 v1)) h v1 h
| EvOP h op n0 n1 : EV O (OP op (P (INT n0) (INT n1))) h (INT (op n0 n1)) h
| EvUNFOLD h v t : EV 1 (UNFOLD (FOLD t v)) h v h
| EvREF (h:Heap) v (l:nat) : l \notin dom h -> EV 1 (REF v) h (LOC l) (updMap l v h)
| EvBANG (h:Heap) v (l:nat) : h l = Some v -> EV 1 (BANG (LOC l)) h v h
| EvASSIGN (h:Heap) v (l:nat) : h l -> EV 1 (ASSIGN (LOC l) v) h UNIT (updMap l v h)
| EvLET h n0 e0 v0 h0 n1 e1 v h1 : EV n0 e0 h v0 h0 -> 
    EV n1 (substE (v0::nil) e1) h0 v h1 -> EV (n0 + n1) (LET e0 e1) h v h1
| EvAPP h n t0 e v0 v h0 : EV n (substE (v::nil) e) h v0 h0 -> 
    EV n (APP (LAM t0 e) v) h v0 h0(*| EvAPP h n t0 t1 e v0 v h0 : EV n (substE (v :: FIX t0 t1 e :: nil) e) h v0 h0 -> EV n (APP (FIX t0 t1 e) v) h v0 h0*)
| EvTAPP h n e t v0 h0 : EV n (etsubst (t::nil) e) h v0 h0 -> 
    EV n (TAPP (TLAM e) t) h v0 h0
| EvCASEL h n t v e0 e1 v0 h0 : EV n (substE (v::nil) e0) h v0 h0 -> 
    EV n (CASE (INL t v) e0 e1) h v0 h0
| EvCASER h n t v e0 e1 v0 h0 : EV n (substE (v::nil) e1) h v0 h0 -> 
    EV n (CASE (INR t v) e0 e1) h v0 h0.
(*=End *)

Definition stty (S:StoreType 0) (h:Heap) :=
   forall l t v, S l = Some t -> h l = Some v -> 0 |- nil | S |v- v ::: t.

Lemma findom_leq_trans T0 (T1:eqType) (f:FinDom T0 T1) f' f'' : findom_leq f f' -> findom_leq f' f'' -> findom_leq f f''.
move => T0 T1 f f' f'' L L'. unfold findom_leq in *. apply (introT (@allP _ _ (dom f))).
move => x D. have a:= elimT (@allP _ _ _) L _ D.
have c:=def_on_dom f x. rewrite D in c. rewrite (eqP a) in c. have d:=def_on_dom f' x. rewrite c in d.
clear c D. have c:=sym_eq d. clear d. have b:= elimT (@allP _ _ _) L' _ c.
rewrite (eqP a). by rewrite (eqP b).
Qed.

Lemma post_comp_id T T' (f:FinDom T T') : post_comp (fun x => Some x) f = f.
move => T T' f. apply findom_ext. simpl. case: f. simpl. move => s _. elim:s ; first by [].
move => t s IH. simpl. rewrite IH. by case: t.
Qed.

Lemma tpres S e t : 0 |- nil | S |e- e ::: t -> forall n v h h', EV n e h v h' -> stty S h -> dom S =i dom h ->
  { S':StoreType 0 & {D:((0 |- nil | S' |v- v ::: t) * stty S' h')%type | findom_leq S S' /\ dom S' =i dom h'}}.
move => S e t T n v h h' ev. elim: n e h v h'/ ev S t T.
- move => h v S t D Sw ED. exists S. rewrite findom_leq_refl. by split ; first by inversion D.
- move => h v0 v1 S t D Sw ED. exists S. rewrite findom_leq_refl. split ; last by []. split ; last by [].
  inversion D. inversion X. by inversion H1.
- move => h v0 v1 S t D Sw ED. exists S. rewrite findom_leq_refl.
  do 2 split ; last by []. inversion D. inversion X. by inversion H1. by []. by [].
- move => h op n0 n1 S t D Sw ED. exists S.
  rewrite findom_leq_refl. do 2 split ; last by []. inversion D. rewrite H0.
  by apply (TvINT nil S _ (refl_equal _)). by []. by [].
- move => h v t S t0 D Sw ED. exists S. rewrite findom_leq_refl. do 2 split ; last by []. simpl. inversion D.
  rewrite H0. clear t0 H0 D. clear e H. inversion X. by inversion H0. by []. by [].
- move => h v l N S t D Sw ED. inversion D. rewrite H0. clear D t H0. clear H e.
  exists (updMap l a S). split. split ; first by apply: (TvLOC _ _ (refl_equal _)) ; by rewrite updMap_simpl.
  move => l0 t0 v0 A B. case_eq (l0 == l) => E.
  + rewrite (eqP E) in A. rewrite updMap_simpl in A. inversion A. rewrite H0 in X. clear a H0 A.
    rewrite (eqP E) in B. rewrite updMap_simpl in B. inversion B. rewrite H0 in X. apply: (LweakV 0 X).
    by rewrite leq_upd ; last by rewrite ED.
  + rewrite updMap_simpl2 in A ; last by rewrite E. rewrite updMap_simpl2 in B ; last by rewrite E. 
    specialize (Sw l0 t0 v0 A B). apply: (LweakV 0 Sw). by rewrite leq_upd ; last by rewrite ED.
  rewrite <- ED in N. rewrite leq_upd ; last by []. split ; first by []. move => i. do 2 rewrite indomUpdMap.
  by rewrite ED.
- move => h v l e S t D Sw ED. exists S. rewrite findom_leq_refl. split ; last by []. split ; last by [].
  inversion D. clear e0 H0. inversion X. clear H l0. inversion H1. rewrite <- H2 in H0. rewrite <- H2. clear t' H1 H2.
  specialize (Sw l t v H0 e). by apply Sw.
- move => h v l Def S t D Sw ED. exists S. rewrite findom_leq_refl. inversion D. rewrite H0. clear t H0 D. clear e H1.
  clear l0 H. split. split ; first by apply TvUNIT.
  move => l0 t0 v0 e0 e1. case_eq (l0 == l) => E.
  + rewrite (eqP E) in e1. rewrite updMap_simpl in e1. inversion e1. rewrite <- H0. clear v0 H0 e1.
    rewrite (eqP E) in e0. clear l0 E. inversion X. inversion H1. rewrite <- H3 in H0. rewrite e0 in H0. inversion H0.
    by apply X0.
  + rewrite (updMap_simpl2) in e1 ; last by rewrite E. specialize (Sw l0 t0 v0 e0 e1). by apply Sw.
  simpl. split ; first by []. move => i. rewrite indomUpdMap. rewrite ED.
  case_eq ((i:nat_compType) == l) => e ; last by [].
  rewrite (eqP e). simpl. rewrite findom_indom. by rewrite Def.
- move => h0 n0 e0 v1 h1 n1 e2 v2 h2 ev0 IH0 ev1 IH1 S t D Sw ED.
  inversion D. clear e e' H0 H1 D. specialize (IH0 S t' X Sw ED).
  case: IH0 => S1. case. case => D1 Sw1 P1. specialize (IH1 S1 t).
  have W0 := LweakE 0 X0 (proj1 P1).
  have ss:=(typing_substE W0 _).
  specialize (ss [:: v1] nil). have IH := IH1 (ss _) Sw1 (proj2 P1).
  have b:= (findom_leq_trans (proj1 P1)). case: IH. case ; first by []. simpl. move => j.
    rewrite nth_default ; last by []. simpl. rewrite nth_default ; last by []. by apply TvUNIT.
  move => S2 ; case => D2 P2. exists S2. rewrite (b _ (proj1 P2)). split. by apply D2. split ; first by [].
  by apply (proj2 P2).
(*- move => h0 n0 t0 t1 e v0 v1 h1 ev0 IH0 S t D Sw ED. apply IH0 ; try by [].
  inversion D. clear rand rator H0 H1. inversion X. clear body H2 t' t'' H H1. inversion H0. rewrite H1 in X, X0.
  clear a H1 H0. rewrite H2 in X. clear D H2 t. apply: (typing_substE X1).
  case ; first by []. case ; first by []. simpl. move => j.
    rewrite nth_default ; last by []. simpl. rewrite nth_default ; last by []. by apply TvUNIT.*)
- move => h0 n0 t0 e v0 v1 h1 ev0 IH0 S t D Sw ED. apply IH0 ; try by [].
  inversion D. clear rand rator H0 H1. inversion X. clear body a0 H H1. inversion H0. rewrite H1 in X, X0.
  clear a H1 H0. rewrite H2 in X. clear D H2 t. apply: (typing_substE X1).
  case ; first by []. simpl. move => j.
    rewrite nth_default ; last by []. simpl. rewrite nth_default ; last by []. by apply TvUNIT.
- move => h0 n e v0 v1 h1 ev0 IH0 S t D Sw ED. apply IH0 ; try by [].
  inversion D. clear e0 H a H1. rewrite H0. clear t H0 D. have c:= (@tsubstE_deriv 1 nil _ _ e).
  simpl in c. unfold idsub. simpl. specialize (c (post_compt (@tshiftL 0 1 _) S) b).
  inversion X. clear H e0. inversion H0. rewrite <- H1. rewrite <- H1 in X0. clear t' H1 H0.
  simpl in X0. specialize (c X0 _ [:: v0]). simpl in c. specialize (c (ltn0Sn _)).
  apply (tsubst_Eeq c) ; first by []. unfold post_compt. rewrite post_comp_comp.
  apply trans_eq with (y:=post_compt id S) ; last by unfold post_compt ; rewrite post_comp_id.
  apply post_comp_eq. move => x. simpl.
  have a:= (@tsubst_shiftLW 1 0 x 0 0 [::v0] nil). by rewrite a ; first by rewrite (tsubst_id x).
- move => h0 n0 t v0 e0 e1 v1 h1 ev IH S t1 D Sw ED. apply IH ; [idtac | by [] | by []].
  inversion D. clear e e' H1 H2. clear v H0.
  apply (typing_substE X0). case. simpl. inversion X. by inversion H0.
  simpl. move => n. rewrite (nth_default UNIT) ; last by []. rewrite (nth_default Unit) ; last by []. by apply TvUNIT.
- move => h0 n0 t v0 e0 e1 v1 h1 ev IH S t1 D Sw ED. apply IH ; [idtac | by [] | by []].
  inversion D. clear e e' H1 H2. clear v H0.
  apply (typing_substE X1). case. simpl. inversion X. by inversion H0.
  simpl. move => n. rewrite (nth_default UNIT) ; last by []. rewrite (nth_default Unit) ; last by []. by apply TvUNIT.
Qed.

Lemma eq_in_all (T:eqType) : forall (a1 a2:pred T) (s:seq T), {in s, a1 =1 a2} -> all a1 s = all a2 s.
move=> T a1 a2; elim => [| x s IHs eq_a] //=.
rewrite eq_a ?mem_head ?IHs // => y s_y; apply: eq_a; exact: mem_behead.
Qed.

Definition heap_closed (h:Heap) := all (fun l => match h l with | None => true | Some v => closedV v end) (dom h).

Lemma heap_closedP (h:Heap) : (forall l v, h l = Some v -> closedV v) <-> heap_closed h.
move => h. split.
move => C. unfold heap_closed. rewrite (@eq_in_all _ _ predT (dom h)) ; first by rewrite all_predT.
move => l I. simpl. specialize (C l). case_eq (h l) ; last by move => E ; rewrite E.
move => v E. rewrite E. specialize (C v E). by apply C.
move => C l v E. unfold heap_closed in C. have A:= (allP C) l. rewrite E in A. rewrite findom_indom in A. rewrite E in A.
by apply A.
Qed.

Record cheap : Type := CHeap {
  heap :> Heap;
  _ : heap_closed heap
}.

Lemma cheapP (h:cheap) : heap_closed h.
by case.
Qed.

Canonical Structure cheap_subType := Eval hnf in [subType for heap by cheap_rect].

Lemma free_var_tsubst n : (forall (v:Value n) l m (s:seq (Ty m)), free_varV v l = free_varV (vtsubst s v) l) /\
                          (forall (e:Exp n) l m (s:seq (Ty m)), free_varE e l = free_varE (etsubst s e) l).
apply ExpValue_ind => n.
- by [].
- by [].
- by [].
- move => e IH l m s. simpl. by rewrite (IH l _ (TVar (ltn0Sn m) :: map (@tshiftL 0 1 _) s)).
- move => t e IH l m s. simpl. by rewrite (IH (0 :: map S l) _ s).
- by [].
- move => v0 IH0 v1 IH1 l m s. simpl. rewrite (IH0 l _ s). by rewrite (IH1 l _ s).
- move => t v IH l m s. simpl. by rewrite (IH l _ s).
- move => t v IH l m s. simpl. by rewrite (IH l _ s).
- move => t v IH l m s. simpl. by rewrite (IH l _ s).
- move => v IH l m s. simpl. by rewrite (IH l _ s).
- move => v IH l m s. simpl. by rewrite (IH l _ s).
- move => v IH l m s. simpl. by rewrite (IH l _ s).
- move => t v IH l m s. simpl. by rewrite (IH l _ s).
- move => v IH l m s. simpl. by rewrite (IH l _ s).
- move => v IH l m s. simpl. by rewrite (IH l _ s).
- move => v IH l m s. simpl. by rewrite (IH l _ s).
- move => v0 IH0 v1 IH1 l m s. simpl. rewrite (IH0 l _ s). by rewrite (IH1 l _ s).
- move => v0 IH0 v1 IH1 l m s. simpl. rewrite (IH0 l _ s). by rewrite (IH1 (O::map S l) _ s).
- move => v0 IH0 v1 IH1 l m s. simpl. rewrite (IH0 l _ s). by rewrite (IH1 l _ s).
- move => v0 IH0 t l m s. simpl. by rewrite (IH0 l _ s).
- move => v0 IH0 v1 IH1 v2 IH2 l m s. simpl. rewrite (IH0 l _ s). rewrite (IH1 (O::map S l) _ s). by rewrite (IH2 (O::map S l) _ s).
Qed.

Definition free_varV_vtsubst n := proj1 (@free_var_tsubst n).
Definition free_varE_etsubst n := proj2 (@free_var_tsubst n).

Lemma closed_tsubst n (e:Exp n.+1) (C:closedE e) m (s:seq (Ty m)) : closedE (etsubst s e).
move => n e C m s. unfold closedE. rewrite <- free_varE_etsubst. by apply C.
Qed.

Lemma free_var_eq n : (forall v:Value n, forall l l', (forall i, (i \in l) = (i \in l')) -> free_varV v l' = free_varV v l) /\
                    (forall e:Exp n, forall l l', (forall i, (i \in l) = (i \in l')) -> free_varE e l' = free_varE e l).
apply ExpValue_ind => n.
- move => j l l'. simpl. move => X. by rewrite (X j).
- by [].
- by [].
- move => e IH l l'. simpl. move => X. by apply (IH l l' X).
- move => t e IH l l'. simpl. move => X. specialize (IH (0 :: map S l) (0 :: map S l')).
  apply IH. move => j. case: j ; first by do 2 rewrite in_cons. move => j. do 2 rewrite in_cons.
  rewrite (mem_map succn_inj l j). rewrite (mem_map succn_inj l' j). simpl. by apply X.
- by [].
- move => v0 IH0 v1 IH1 l l' X. simpl. rewrite (IH0 _ _ X). by rewrite (IH1 _ _ X).
- move => t v IH l l' X. simpl. by apply (IH _ _ X).
- move => t v IH l l' X. simpl. by apply (IH _ _ X).
- move => t v IH l l' X. simpl. by apply (IH _ _ X).
- move => v IH l l' X. simpl. by apply (IH _ _ X).
- move => v IH l l' X. simpl. by apply (IH _ _ X).
- move => v IH l l' X. simpl. by apply (IH _ _ X).
- move => op v IH l l' X. simpl. by apply (IH _ _ X).
- move => v IH l l' X. simpl. by apply (IH _ _ X).
- move => v IH l l' X. simpl. by apply (IH _ _ X).
- move => v IH l l' X. simpl. by apply (IH _ _ X).
- move => v0 IH0 v1 IH1 l l' X. simpl. rewrite (IH0 _ _ X). by rewrite (IH1 _ _ X).
- move => e0 IH0 e1 IH1 l l'. simpl. move => X. rewrite (IH0 _ _ X).
  specialize (IH1 (0 :: map S l) (0 :: map S l')).
  rewrite IH1 ; first by []. move => j. case: j ; first by do 2 rewrite in_cons. move => j. do 2 rewrite in_cons.
  rewrite (mem_map succn_inj l j). rewrite (mem_map succn_inj l' j). simpl. by apply X.
- move => v0 IH0 v1 IH1 l l' X. simpl. rewrite (IH0 _ _ X). by rewrite (IH1 _ _ X).
- move => v0 IH0 t l l' X. simpl. by rewrite (IH0 _ _ X).
- move => e0 IH0 e1 IH1 e2 IH2 l l'. simpl. move => X. rewrite (IH0 _ _ X).
  specialize (IH1 (0 :: map S l) (0 :: map S l')). simpl.
  specialize (IH2 (0 :: map S l) (0 :: map S l')).
  rewrite IH1. simpl. rewrite IH2 ; first by [].
  + move => j. case: j ; first by do 2 rewrite in_cons. move => j. do 2 rewrite in_cons.
    rewrite (mem_map succn_inj l j). rewrite (mem_map succn_inj l' j). simpl. by apply X.
  + move => j. case: j ; first by do 2 rewrite in_cons. move => j. do 2 rewrite in_cons.
    rewrite (mem_map succn_inj l j). rewrite (mem_map succn_inj l' j). simpl. by apply X.
Qed.

Definition free_varV_eq n := proj1 (@free_var_eq n).
Definition free_varE_eq n := proj2 (@free_var_eq n).

Lemma free_var_shift n : 
(forall (v:Value n) l k i l', (forall i', i' \in l' -> k <= i' < k + i) -> free_varV (shiftV k i v) (l' ++ map (fun x => if x < k then x else x + i) l) = free_varV v l) /\
(forall (v:Exp n) l k i l', (forall i', i' \in l' -> k <= i' < k + i) -> free_varE (shiftE k i v) (l' ++ map (fun x => if x < k then x else x + i) l) = free_varE v l).
have I:forall k i, injective (fun x : nat => if x < k then x else x + i).
move => k i x y. case_eq (x < k) => L.
- case_eq (y < k) ; first by [].
  rewrite ltnNge. move => L'. have G:=negbFE L'.
  clear L'. move => E. rewrite E in L. clear E. have X:=leq_ltn_trans (leq_addr i y) L.
  have F:=leq_ltn_trans G X. by rewrite ltnn in F.
- case_eq (y < k) => A.
  + rewrite ltnNge in L. have LL:=negbFE L. clear L. move => E. have G:=ssrnat.leq_trans LL (leq_addr i x).
    rewrite E in G. have F:=ssrnat.leq_trans A G. by rewrite ltnn in F.
  + move => A'. have A'':x + i == y + i by rewrite A'.
    rewrite (eqn_addr i x y) in A''. by rewrite (eqP A'').
apply ExpValue_ind => n.
- move => j l k i l' X. simpl. case_eq (j < k) => L.
  + simpl. rewrite mem_cat. specialize (X j). case_eq (j \in l') => A.
    * specialize (X A). rewrite ltnNge in L. have LL:=negbTE L. by rewrite LL in X.
    * rewrite A. refine (trans_eq _ (mem_map (I k i) l j)). by rewrite L.
  + simpl. rewrite mem_cat. case_eq (j + i \in l') => A.
    * specialize (X (j+i) A). have Y:= proj2 (andP X). rewrite (ltn_add2r i) in Y. by rewrite L in Y.
    * refine (trans_eq _ (mem_map (I k i) l j)). rewrite A. by rewrite L.
- by [].
- by [].
- move => e IH l k i. simpl. by apply IH.
- move => t e IH l k i l' X. simpl. specialize (IH (O::map S l) k.+1 i (map S l')). simpl in IH. rewrite map_map in IH.
  rewrite map_cat. rewrite map_map. rewrite <- IH. apply free_varE_eq. move => j. rewrite mem_cat. do 2 rewrite in_cons.
  rewrite mem_cat.
  case: j.
  + rewrite eq_refl. by rewrite orbT.
  + move => x. simpl. case_eq (x.+1 \in map S l') => E ; first by rewrite E.
    rewrite E. simpl. f_equal. f_equal. apply eq_map. clear x E. move => x. simpl.
    case_eq (x < k) => L.
  + have LL:x.+1 < k.+1 by apply L. by rewrite LL.
  + have LL:x.+1 < k.+1 = false by apply L. rewrite LL. by rewrite addSn.
  case. simpl. clear IH X. elim l' ; first by []. move => nn s IH. simpl. rewrite in_cons. simpl. by apply IH.
    move => j A. rewrite (mem_map succn_inj) in A. specialize (X j A). by apply X.
- by [].
- move => v0 IH0 v1 IH1 l k i l' X. simpl. rewrite (IH0 l k i l' X). by rewrite (IH1 l k i l' X).
- move => t v IH l k i l' X. simpl. by rewrite (IH l k i l' X).
- move => t v IH l k i l' X. simpl. by rewrite (IH l k i l' X).
- move => t v IH l k i l' X. simpl. by rewrite (IH l k i l' X).
- move => v IH l k i l' X. simpl. by rewrite (IH l k i l' X).
- move => v IH l k i l' X. simpl. by rewrite (IH l k i l' X).
- move => v IH l k i l' X. simpl. by rewrite (IH l k i l' X).
- move => t v IH l k i l' X. simpl. by rewrite (IH l k i l' X).
- move => v IH l k i l' X. simpl. by rewrite (IH l k i l' X).
- move => v IH l k i l' X. simpl. by rewrite (IH l k i l' X).
- move => v IH l k i l' X. simpl. by rewrite (IH l k i l' X).
- move => v0 IH0 v1 IH1 l k i l' X. simpl. rewrite (IH0 l k i _ X). by rewrite (IH1 l k i _ X).
- move => e0 IH0 e1 IH1 l k i l' X. simpl. rewrite (IH0 l k i _ X).
  specialize (IH1 (0 :: map S l) k.+1 i (map S l')). simpl in IH1. rewrite map_map in IH1.
  rewrite map_cat.
  rewrite map_map. rewrite <- IH1. case (free_varE e0 l) ; last by []. simpl.
  apply free_varE_eq. move => j. rewrite mem_cat. do 2 rewrite in_cons.
  rewrite mem_cat.
  case: j.
  + rewrite eq_refl. by rewrite orbT.
  + move => x. simpl. case_eq (x.+1 \in map S l') => E ; first by rewrite E.
    rewrite E. simpl. f_equal. f_equal. apply eq_map. clear x E. move => x. simpl.
    case_eq (x < k) => L.
  + have LL:x.+1 < k.+1 by apply L. by rewrite LL.
  + have LL:x.+1 < k.+1 = false by apply L. rewrite LL. by rewrite addSn.
  case. simpl. clear IH1 X. elim l' ; first by []. move => nn s IH. simpl. rewrite in_cons. simpl. by apply IH.
    move => j A. rewrite (mem_map succn_inj) in A. specialize (X j A). by apply X.
- move => v0 IH0 v1 IH1 l k i l' X. simpl. rewrite (IH0 l k i _ X). by rewrite (IH1 l k i _ X).
- move => v0 IH0 t l k i l' X. simpl. by rewrite (IH0 l k i l' X).
- move => e0 IH0 e1 IH1 e2 IH2 l k i l' X. simpl. rewrite (IH0 l k i l' X).
  specialize (IH1 (0 :: map S l) k.+1 i (map S l')). simpl in IH1. rewrite map_map in IH1.
  rewrite map_cat. rewrite map_map. case (free_varV e0 l) ; last by []. simpl.
  rewrite <- IH1.
  specialize (IH2 (0 :: map S l) k.+1 i (map S l')). simpl in IH2. rewrite map_map in IH2. rewrite <- IH2.
  f_equal. apply free_varE_eq. move => j. rewrite mem_cat. do 2 rewrite in_cons.
  rewrite mem_cat.
  case: j.
  + rewrite eq_refl. by rewrite orbT.
  + move => x. simpl. case_eq (x.+1 \in map S l') => E ; first by rewrite E.
    rewrite E. simpl. f_equal. f_equal. apply eq_map. clear x E. move => x. simpl.
    case_eq (x < k) => L.
  + have LL:x.+1 < k.+1 by apply L. by rewrite LL.
  + have LL:x.+1 < k.+1 = false by apply L. rewrite LL. by rewrite addSn.
apply free_varE_eq. move => j. rewrite mem_cat. do 2 rewrite in_cons.
  rewrite mem_cat.
  case: j.
  + rewrite eq_refl. by rewrite orbT.
  + move => x. simpl. case_eq (x.+1 \in map S l') => E ; first by rewrite E.
    rewrite E. simpl. f_equal. f_equal. apply eq_map. clear x E. move => x. simpl.
    case_eq (x < k) => L.
  + have LL:x.+1 < k.+1 by apply L. by rewrite LL.
  + have LL:x.+1 < k.+1 = false by apply L. rewrite LL. by rewrite addSn.
  case. simpl. clear IH1 X. elim l' ; first by []. move => nn s IH. simpl. rewrite in_cons. simpl. by apply IH.
    move => j A. rewrite (mem_map succn_inj) in A. specialize (X j A). by apply X.
  case. simpl. clear IH1 X. elim l' ; first by []. move => nn s IH. simpl. rewrite in_cons. simpl. by apply IH.
    move => j A. rewrite (mem_map succn_inj) in A. specialize (X j A). by apply X.
Qed.

Definition free_varV_shiftV n := proj1 (@free_var_shift n).
Definition free_varE_shiftE n := proj2 (@free_var_shift n).

Lemma closed_sub n : 
(forall (v:Value n) s l, all (fun v => free_varV v l) s -> free_varV (substV s v) l) /\
(forall (v:Exp n) s l, all (fun v => free_varV v l) s -> free_varE (substE s v) l).
apply ExpValue_ind => n.
- move => j s l' Y. simpl. elim: s Y j ; first by move => _ ; case.
    move => v s IH X j. simpl. case: j. simpl in X. simpl. by apply (proj1 (andP X)).
     move => j. simpl. apply IH. by apply (proj2 (andP X)).
- by [].
- by [].
- move => e IH s l.  simpl. move => A. apply IH. rewrite all_map.
  rewrite (@eq_all _ _ ((fun x => free_varV x l)) _ s) ; first by apply A.
  move => v. simpl. by apply (sym_eq (free_varV_vtsubst _ _ _)).
- move => t e IH s l X. simpl. apply IH. simpl. rewrite all_map.
  rewrite (@eq_all _ _ (fun x => free_varV x l) _ s) ; first by apply X.
  move => x. simpl. have A:= (@free_varV_shiftV _ x l 0 1 [:: O]). simpl in A.
  rewrite <- A ; last by case. f_equal. f_equal. apply eq_map. move => aa. simpl. by rewrite addnC.
- by [].
- move => v0 IH0 v1 IH1 s l A. simpl. rewrite (IH0 _ _ A). by rewrite (IH1 _ _ A).
- move => t v IH s l A. simpl. by apply IH.
- move => t v IH s l A. simpl. by apply IH.
- move => t v IH s l A. simpl. by apply IH.
- move => v IH s l A. simpl. by apply IH.
- move => v IH s l A. simpl. by apply IH.
- move => v IH s l A. simpl. by apply IH.
- move => op v IH s l A. simpl. by apply IH.
- move => v IH s l A. simpl. by apply IH.
- move => v IH s l A. simpl. by apply IH.
- move => v IH s l A. simpl. by apply IH.
- move => v0 IH0 v1 IH1 s l A. simpl. rewrite (IH0 _ _ A). by rewrite (IH1 _ _ A).
- move => e0 IH0 e1 IH1 s l A. simpl. rewrite (IH0 _ _ A). simpl.
  apply IH1. simpl. rewrite all_map.
  rewrite (@eq_all _ _ (fun x => free_varV x l) _ s) ; first by apply A.
  move => x. simpl. have B:= (@free_varV_shiftV _ x l 0 1 [:: O]). simpl in B.
  rewrite <- B ; last by case. f_equal. f_equal. apply eq_map. move => aa. simpl. by rewrite addnC.
- move => v0 IH0 v1 IH1 s l A. simpl. rewrite (IH0 _ _ A). by rewrite (IH1 _ _ A).
- move => v IH t s l A. simpl. by apply IH.
- move => e0 IH0 e1 IH1 e2 IH2 s l A. simpl. rewrite (IH0 _ _ A). simpl.
  rewrite IH2 ; simpl. rewrite IH1 ; simpl ; first by simpl.
  rewrite all_map.
  rewrite (@eq_all _ _ (fun x => free_varV x l) _ s) ; first by apply A.
  move => x. simpl. have B:= (@free_varV_shiftV _ x l 0 1 [:: O]). simpl in B.
  rewrite <- B ; last by case. f_equal. f_equal. apply eq_map. move => aa. simpl. by rewrite addnC.
  rewrite all_map.
  rewrite (@eq_all _ _ (fun x => free_varV x l) _ s) ; first by apply A.
  move => x. simpl. have B:= (@free_varV_shiftV _ x l 0 1 [:: O]). simpl in B.
  rewrite <- B ; last by case. f_equal. f_equal. apply eq_map. move => aa. simpl. by rewrite addnC.
Qed.

Definition closedV_sub n := proj1 (@closed_sub n).
Definition closedE_sub n := proj2 (@closed_sub n).

Lemma map_closed n (s:seq (cvalue n)) : all (fun x => free_varV x nil) (map (@cval _) s).
move => n. elim ; first by [].
move => v s IH. simpl. rewrite IH. rewrite andbT. by apply (cvalueP v).
Qed.

Definition csubstE n (s:seq (cvalue n)) (e:Exp n) : cexpression n := @CExp _ (substE (map (@cval n) s) e) (closedE_sub e (map_closed s)).
Canonical Structure csubstV (n:nat) (s:seq (cvalue n)) (v:Value n) := CValue _ (closedV_sub v (map_closed s)).

Lemma negbF_imp (b:bool) : (b -> False) -> b = false.
case ; last by []. move => A. by specialize (A is_true_true).
Qed.

Lemma ev_closed n e v h h' : EV n e h v h' -> closedE e -> heap_closed h -> heap_closed h' /\ closedV v.
move => n e v h h' ev. elim: n e v h h' / ev.
- move => h v A B. split ; first by apply B. by apply A.
- move => h v0 v1 A B. split ; first by []. apply (proj1 (andP A)).
- move => h v0 v1 A B. split ; first by []. apply (proj2 (andP A)).
- by [].
- by [].
- move => h v l D C H. split ; last by []. apply (proj1 (heap_closedP (updMap l v h))).
  move => l' v'. case_eq (l == l') => E.
  + rewrite (eqP E). rewrite updMap_simpl. case => e ; first by unfold closedE in C ; rewrite <- e ; apply C.
  + rewrite (updMap_simpl2). move => A. by apply (proj2 (heap_closedP h) H _ _ A).
    apply negbT. by apply negbF_imp => e0 ; rewrite (eqP e0) in E ; rewrite eq_refl in E.
- move => h v l E C H. split ; first by []. by apply (proj2 (heap_closedP h) H _ _ E).
- move => h v l D C H. split ; last by []. apply (proj1 (heap_closedP _)). move => l' v' e. case_eq (l == l') => E.
  + rewrite (eqP E) in e. rewrite updMap_simpl in e. case: e => e. rewrite <- e. by apply C.
  + rewrite updMap_simpl2 in e. by apply (proj2 (heap_closedP _) H _ _ e).
    apply negbT. by apply negbF_imp => e0 ; rewrite (eqP e0) in E ; rewrite eq_refl in E.
- move => h n0 e0 v0 h0 n1 e1 vr h1 ev0 IH0 ev1 IH1 C H. specialize (IH0 (proj1 (andP C)) H).
  have IH1':= IH1 (@closedE_sub _ e1 [:: v0] nil _). clear IH1. simpl in IH1'. rewrite andbT in IH1'.
  by apply (IH1' (proj2 IH0) (proj1 IH0)).
- move => h n t e v v' h' ev IH C H. have IH' := IH (@closedE_sub _ e [:: v'] nil _). simpl in IH'. rewrite andbT in IH'.
  specialize (IH' (proj2 (andP C)) H). by apply IH'.
- move => h n e t v h' ev IH C H. have A:=(@free_varE_etsubst _ e nil _ [:: t]). unfold closedE in IH. rewrite <- A in IH.
  specialize (IH C H). by apply IH.
- move => h n t v e0 e1 v0 h0 ev IH C H.
  have IH':= IH (@closedE_sub _ e0 [:: v] nil _). clear IH. simpl in IH'. rewrite andbT in IH'.
  by apply (IH' (proj1 (andP (proj1 (andP C)))) H).
- move => h n t v e0 e1 v0 h0 ev IH C H.
  have IH':= IH (@closedE_sub _ e1 [:: v] nil _). clear IH. simpl in IH'. rewrite andbT in IH'.
  by apply (IH' (proj1 (andP (proj1 (andP C)))) H).
Qed.

Lemma cev n (e:cexpression O) v (h:cheap) h' : EV n e h v h' -> heap_closed h' /\ closedV v.
move => n e v h h' ev. by apply (@ev_closed n e v h h' ev (cexpP e) (cheapP h)).
Qed.

