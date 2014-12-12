(**********************************************************************************
 * msem.v                                                                         *
 * Formalizing Domains, Ultrametric Spaces and Semantics of Programming Languages *
 * Nick Benton, Lars Birkedal, Andrew Kennedy and Carsten Varming                 *
 * July 2010                                                                      *
 * Build with Coq 8.2pl1 plus SSREFLECT                                           *
 **********************************************************************************)

(* semantics of types for the kitchen sink language *)

Require Import MetricRec mpremet msyntax moperational.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(** printing \in %\ensuremath{\in}% *)
(** printing R0 %\ensuremath{R_0}% *)
(** printing R1 %\ensuremath{R_1}% *)
(** printing n0 %\ensuremath{n_0}% *)
(** printing n1 %\ensuremath{n_1}% *)
(** printing j0 %\ensuremath{j_0}% *)
(** printing j1 %\ensuremath{j_1}% *)
(** printing halve_pcmType %\ensuremath{\frac{1}{2}}% *)

Open Scope C_scope.
Open Scope M_scope.

(*=MetBF *)
Definition BF : BiFunctor pcmECatType := findomBF
 ((BiComp (halveBF idBF) (constBF (upred_pcmType (cvalue O))) BiArrow))
                                                         [compType of nat]. (*CLEAR*)
Lemma BF_ob A B : ob BF A B =
  findom_pcmType [compType of nat] ((halve_pcmType A -=> upred_pcmType (cvalue O))).
by [].
Qed.

Lemma morph_contractive A B C D : contractive (MetricRec.morph BF A B C D).
move => A B C D. unfold BF. apply findom_BF_contractive.
apply comp_BF_contractive ; last by apply constBF_contractive. by apply halve_morph_contractive.
Qed.

Module Type RecMet.

Variable W : pcmType.
Variable Unfold : W =-> findom_pcmType [compType of nat] ((halve_pcmType W -=> upred_pcmType (cvalue O))).
Variable Fold : findom_pcmType [compType of nat] ((halve_pcmType W -=> upred_pcmType (cvalue O))) =-> W.

Variable FU_id : Fold << Unfold =-= Id.
Variable UF_id : Unfold << Fold =-= Id.

End RecMet.

Module Solution : RecMet.

(*CLEARED*) 
Definition W : pcmType := @DInf BF morph_contractive.
Definition Unfold := @Unfold BF morph_contractive :
  W =-> findom_pcmType [compType of nat]
                         ((halve_pcmType W -=> upred_pcmType (cvalue O))).
Definition Fold  := @Fold BF morph_contractive :
  findom_pcmType [compType of nat]
                   ((halve_pcmType W -=> upred_pcmType (cvalue O))) =-> W.
(*=End *)

Lemma FU_id : Fold << Unfold =-= Id.
apply (@FU_iso BF morph_contractive).
Qed.

Lemma UF_id : Unfold << Fold =-= Id.
apply (@UF_iso BF morph_contractive).
Qed.

End Solution.

Notation W := Solution.W.
Notation Fold := Solution.Fold.
Notation Unfold := Solution.Unfold.

Definition FU_id := Solution.FU_id.
Definition UF_id := Solution.UF_id.

Open Scope O_scope.

Lemma Fold_monic x y : Fold x <= Fold y -> x <= y.
move => x y X. have M:=fmonotonic Unfold X. have e:= (UF_id x). have e':=UF_id y.
apply (pcm_respect e e' M).
Qed.

Lemma Unfold_monic x y : Unfold x <= Unfold y -> x <= y.
move => x y X. have M:=fmonotonic Fold X. have e:= (FU_id x). have e':=FU_id y.
apply (pcm_respect e e' M).
Qed.

Lemma Unfold_antinonexp n (w w':W) : Unfold w = n = Unfold w' -> w = n = w'.
move => n w w' X. have Y:=fnonexpansive Fold X. clear X.
apply (Mrel_trans (Msym (proj2 (Mrefl _ _) (FU_id w) n))).
refine (Mrel_trans _ (proj2 (Mrefl _ _) (FU_id w') n)). by apply Y.
Qed.

Lemma Fold_antinonexp n w w' : Fold w = n = Fold w' -> w = n = w'.
move => n w w' X. have Y:=fnonexpansive Unfold X. clear X.
apply (Mrel_trans (Msym (proj2 (Mrefl _ _) (UF_id w) n))).
refine (Mrel_trans _ (proj2 (Mrefl _ _) (UF_id w') n)). by apply Y.
Qed.

Lemma less_nil j (P:j < 0) : False.
move => j. by rewrite ltn0.
Qed.

(*=TV *)
Definition TV := halve_pcmType W -=> upred_pcmType (cvalue O).
Fixpoint TVal (n:nat) : cmetricType :=
match n with | O => One | S n => TVal n * TV end.

Fixpoint pick n j : (j < n) -> cmetricCatType (TVal n) TV :=
match n as n0, j as j0 return j0 < n0 -> TVal n0 =-> TV with
| O,_ => fun F => match less_nil F with end
| S n,S j => fun F => @pick n j F << pi1
| S n, O => fun F => pi2
end.
(*=End *)
  
Lemma pick_top n X : (@pick n.+1 0 X) = pi2.
by [].
Qed.

Lemma pick_rest n i X : (@pick n.+1 i.+1 X) = @pick n i X << pi1.
by [].
Qed.

Lemma upred_prod_down (X:(upred_metricType (cvalue O) * upred_metricType (cvalue O))) :
   downclosed (fun kt => let (v,p) := snd kt:(cvalue O) in
                             match v as v0 return closedV v0 -> Prop with 
                               | P v0 v1 =>
                                    fun D => upred_fun (fst X) (fst kt, CValue v0 (proj1 (andP D))) /\
                                             upred_fun (snd X) (fst kt, CValue v1 (proj2 (andP D)))
                               | _ => fun _ => False end p).
move => X k k'. case => v P L. simpl. case: v P ; try by [].
move => v0 v1 P [A B].
split ; first by apply (upred_downclosed (ltnW L) A). by apply (upred_downclosed (ltnW L) B).
Qed.

Open Scope C_scope.
Open Scope M_scope.

Definition upred_prod (p:((upred_cmetricType (cvalue O)) * (upred_cmetricType (cvalue O))) %CAT)
  : upred_cmetricType (cvalue O) := exist (@downclosed _) _ (@upred_prod_down p).

Lemma upred_product_ne : nonexpansive upred_prod.
move => n.
case => x0 x1. case => y0 y1. case => e0 e1.
move => k v L. case: v. simpl. case ; try by [].
move => v0 v1 P. specialize (e0 k (CValue _ (proj1 (andP P))) L).
specialize (e1 k (CValue _ (proj2 (andP P))) L). simpl in e0,e1. rewrite e0. by rewrite e1.
Qed.

Definition upred_productN : metricCatType (upred_pcmType (cvalue O) * upred_pcmType (cvalue O)) (upred_pcmType (cvalue O)) := Eval hnf in mk_fmet upred_product_ne.

Lemma upred_product_mono : monotonic upred_productN.
case => x0 x1. case => y0 y1. case => e0 e1. case => k. case.
simpl. case ; try by [].
move => v0 v1 P. specialize (e0 (k,(CValue _ (proj1 (andP P))))).
specialize (e1 (k,(CValue _ (proj2 (andP P))))). move => [A B]. split ; by [apply e0 | apply e1].
Qed.

Definition upred_product : (upred_pcmType (cvalue O) * upred_pcmType (cvalue O) =-> upred_pcmType (cvalue O)) :=
  Eval hnf in mk_fpcm upred_product_mono.

Add Parametric Morphism : @upred_product
with signature (@tset_eq ((upred_pcmType (cvalue 0) * upred_pcmType (cvalue 0))%CAT)) ==> (@tset_eq (upred_pcmType (cvalue 0)))
as upred_product_eq_compat.
case => x y. case => x' y'. case => e0 e1. case => k v. simpl. case: v. case ; try done.
move => v0 v1 C. simpl in e1,e0. specialize (e0 (k,CValue _ (proj1 (andP C)))).
specialize (e1 (k,CValue _ (proj2 (andP C)))). rewrite e0. by rewrite e1.
Qed.

Definition upred_sumt (p:upred_cmetricType (cvalue O) * upred_cmetricType (cvalue O)) : upred_cmetricType (cvalue O).
move => X. exists (fun kt => let (v,p) := snd kt:cvalue O in 
                             match v as v0 return closedV v0 -> Prop with
                               | (INL _ p0) => fun P => upred_fun (fst X) (fst kt, CValue p0 P)
                               | (INR _ p0) => fun P => upred_fun (snd X) (fst kt, CValue p0 P)
                               | _ => fun P => False end p).
move => k k'. case => v P L. simpl. case: v P ; try by [] ;
by move => t' v P A ; apply (upred_downclosed (ltnW L) A).
Defined.

Lemma upred_sum_ne : nonexpansive upred_sumt.
move => n.
case => x0 x1. case => y0 y1. case => e0 e1.
move => k. case => v P L. simpl. case: v P ; try by [].
- move => t v P. by rewrite (e0 k (CValue v P) L).
- move => t v P. by rewrite (e1 k (CValue v P) L).
Qed.

Definition upred_sumN : metricCatType (upred_pcmType (cvalue O) * upred_pcmType (cvalue O)) (upred_pcmType (cvalue O)) := Eval hnf in mk_fmet upred_sum_ne.

Lemma upred_sum_mono : monotonic upred_sumN.
case => x0 x1. case => y0 y1. case => e0 e1. case => k. case => v P.
simpl. case: v P ; try by [].
- move => t v P. by apply (e0 (k,(CValue v P))).
- move => t v P. by apply (e1 (k,(CValue v P))).
Qed.

Definition upred_sum : (upred_pcmType (cvalue O) * upred_pcmType (cvalue O) =-> upred_pcmType (cvalue O)) := 
  Eval hnf in mk_fpcm upred_sum_mono.

Add Parametric Morphism : @upred_sum
with signature (@tset_eq ((upred_pcmType (cvalue 0) * upred_pcmType (cvalue 0))%CAT)) ==> (@tset_eq (upred_pcmType (cvalue 0)))
as upred_sum_eq_compat.
case => x y. case => x' y'. case => e0 e1. case => k v. simpl. by case: v; case.
Qed.

(*=upred_mu_down *)
Lemma upred_mu_down n 
   (R: TVal n.+1 =-> halve_pcmType W -=> upred_pcmType (cvalue O)) (s:TVal n)
   (P:(halve_pcmType W =-> upred_pcmType (cvalue O)) * halve_pcmType W) :
downclosed (fun kt => let: CValue v' p' := snd kt in
  match fst kt, v' as v0 return closedV v0 -> Prop with
 | O,FOLD t v => fun X => True
 | S k,FOLD t v => fun X => upred_fun (R ((s,(fst P))) (snd P)) (k,CValue v X)
 | _,_ => fun X => False
  end p').
(*=End *)
move => n R s P. case ; first by []. move => m k. simpl. case => v p L. case: v p ; try done.
move => t v p. case: k L ; first by []. move => k L.
refine (upred_downclosed _). by apply (ssrnat.ltn_trans (ltnSn k) L).
Qed.

(*=upred_mut *)
Definition upred_mut n R s w : upred_pcmType (cvalue O) := 
  exist (@downclosed _) _ (@upred_mu_down n R s w).
(*=End *)

Definition ne_mono (M:cmetricType) (P Q:pcmType) (f:M * P -> Q) :=
   (nonexpansive f) /\ forall m, monotonic (fun x => f (m,x)).

Lemma ne_mono_ne2 (M:cmetricType) (P Q:pcmType) (f:M * P -> Q) (X:ne_mono f) (m:M) : nonexpansive (fun x : P => f (m, x)).
move => M P Q f X m n x x' e. by apply (proj1 X).
Qed.

Definition ne_monoN M P Q f (X:@ne_mono M P Q f) (m:M) : P =-> Q := Eval hnf in mk_fpcmX (ne_mono_ne2 X m) ((proj2 X) m).

Lemma mk_nemon_ne M P Q f (X:@ne_mono M P Q f) : nonexpansive (ne_monoN X).
move => M P Q f X n m m' e x. simpl. by apply ((proj1 X)).
Qed.

Definition mk_nemon M P Q f (X:@ne_mono M P Q f) : M =-> (P -=> Q) := Eval hnf in mk_fmet (mk_nemon_ne X).

(*upred_muS *)
Lemma upred_mu_ne n R s : ne_mono (@upred_mut n R s).
(*=End *)
move => n R s. split.
- move => m. case => f w. case => f' w'. case. case:m ; first by [].
  move => m e e' k. simpl. case => v p L. case: v p ; try done.
  move => t v p. simpl. have d:(R (s, f)) = m.+1 = (R (s, f')) by apply fnonexpansive.
  specialize (d w). have dd:=fnonexpansive ( (R (s, f'))) e'.
  case: k L ; first by []. move => k L. apply ((Mrel_trans d dd) k (CValue v p)). by apply (ssrnat.ltn_trans (ltnSn k) L).
- move => f. simpl in f. move => w w' L. case => k. case. simpl. case ; try done.
  move => t v p. case: k; first by []. move => k. simpl in w,w'.
  have e:(R (s, f)) w <= (R (s, f)) w' by apply: fmonotonic.
  by apply (e _).
Qed.

Definition upred_mup n (R:TVal n.+1 =-> halve_pcmType W -=> upred_pcmType (cvalue O)) (s:TVal n) :
   cmetricCatType (halve_pcmType W -=> upred_pcmType (cvalue O)) (halve_pcmType W -=> (upred_pcmType (cvalue O))) :=
   Eval hnf in mk_nemon (upred_mu_ne R s).

Lemma upred_muC n R (s:TVal n) : contractive (upred_mup R s).
move => n R s m. move => f g e.
move => w. simpl. move => k. case. case ; try done. case: k ; first by []. move => k t v p L.
have d:(R (s, f)) = m = (R (s, g)) by apply fnonexpansive.
apply: d. by apply L.
Qed.

Definition upred_muc n (R: TVal n.+1 =-> halve_pcmType W -=> upred_pcmType (cvalue O)) (s:TVal n) : 
  morphc_pcmType (halve_pcmType W -=> upred_pcmType (cvalue O)) (halve_pcmType W -=> upred_pcmType (cvalue O)) :=
exist _ (upred_mup R s) (upred_muC R s).

Lemma upred_mun n R : nonexpansive (@upred_muc n R).
move => n R m s s' e f w. case: m e ; first by []. move => m e k. simpl. case.
case ; try done. move => t v p. case: k ; first by []. move => k L.
simpl. have d:(R (s, f)) = m.+1 = (R (s', f)) by apply fnonexpansive.
apply (d w k _). by apply (ssrnat.ltn_trans (ltnSn k) L).
Qed.

(*=upred_mu *)
Definition upred_mu n (R: TVal n.+1 =-> halve_pcmType W -=> upred_pcmType (cvalue O)) :
   TVal n =-> morphc_pcmType TV TV := 
    Eval hnf in mk_fmet (@upred_mun n R).
(*=End *)

Lemma heap_cl h l (I:l \in dom (heap h)) : closedV (indom_app I).
move => h l I. have I':=I. rewrite findom_indom in I'.
case_eq (heap h l) ; last by move => E ; rewrite E in I'.
move => v E. clear I'. have e:= indom_app_eq I. rewrite E in e. case: e => e. rewrite e.
by apply (proj2 (heap_closedP h) (cheapP h) l _ E).
Qed.

(*=heap_world *)
Definition heap_world k (h:cheap) (w:W) := 
    forall j, j < k -> dom (heap h) = dom (Unfold w) /\
    forall l (I: l \in dom (Unfold w)) (I':l \in dom (heap h)), 
             upred_fun (indom_app I w) (j,CValue (indom_app I') (heap_cl I')).
(*=End *)
(*=IExp *)
Definition IExp (f:TV) (k:nat) (e:cexpression 0) (w:W) :=
   forall j, (j <= k)%N -> 
   forall (h h':cheap) v (D:EV j e h v h'), heap_world k h w ->
    exists w':W, w <= w' /\ heap_world (k - j) h' w' /\ 
                 upred_fun (f w') (k-j,CValue v (proj2 (cev D))).
(*=End *)
Lemma IExp_respect (f f':TV) (k:nat) (e:cexpression 0) (w:W) : f =-= f' -> IExp f k e w =-= IExp f' k e w.
move => f f' k e w E. unfold IExp. split.
- move => X j L h h' v ev hv. specialize (X j L h h' v ev hv). destruct X as [w' [LL [HV Y]]].
  exists w'. split ; first by []. split ; first by []. specialize (E w').
  have E':f w' =-= f' w' by apply E. clear E. case: (f' w') E' => g Pg. simpl. case: (f w') Y => g' Pg' Y.
  move => X. specialize (X (k-j,CValue _ (proj2 (cev ev)))). rewrite <- X. by apply Y.
- move => X j L h h' v ev hv. specialize (X j L h h' v ev hv). destruct X as [w' [LL [HV Y]]].
  exists w'. split ; first by []. split ; first by []. specialize (E w').
  have E':f w' =-= f' w' by apply E. clear E. specialize (E' (k-j,CValue _ (proj2 (cev ev)))). rewrite E'. by apply Y.
Qed.

Lemma upred_all_down n (R:TVal n.+1 =-> halve_pcmType W -=> upred_pcmType (cvalue 0))
  (s:TVal n * halve_pcmType W) : downclosed (fun kt => let: (k,v) := kt in
   match @cval O v as v0 return closedV v0 -> Prop with
    | TLAM v => fun C => forall (t:Ty 0) (r:TV) (w':W) j, (j <= k)%N -> snd s <= w' ->
             (IExp (R (fst s,r)) j (CExp (etsubst [:: t] v) (@closed_tsubst _ v C _ [:: t])) w')
    | _ => fun _ => False
   end (cvalueP v)).
move => n R s m k v L. simpl. case: v => v C. simpl. case: v C ; try done. case: s => e w.
move => E C X t r w' j L'. simpl. move => LL. simpl in X. apply X. by apply (leqW (leq_ltn_trans L' L)). by apply LL.
Qed.

Definition upred_allt n R s : upred_pcmType (cvalue 0) := exist (@downclosed _) _ (@upred_all_down n R s).

Lemma world_extend n (w0 w1 v0 : W) : w0 = n = v0 -> w0 <= w1 -> exists v1:W, w1 = n = v1 /\ v0 <= v1.
case. move => w0 w1 v0 _ L. by exists v0.
move => n w0 w1 v0 e l.
exists (Fold (create_findomF (Unfold w1) (fun x => match Unfold v0 x with | None => Unfold w1 x | Some v => Some v end))).
have e':=fnonexpansive ( Unfold) e. clear e. split.
have A:=proj1 e'. have B:=proj2 e'. clear e'.
apply Unfold_antinonexp.
refine (Mrel_trans _ (proj2 (Mrefl _ _) (tset_sym (UF_id _)) _)).
split.
- rewrite dom_create_findomF.
  apply trans_eq with (y:=filter some (dom (Unfold w1))) ; first by rewrite filter_some.
  apply: eq_in_filter. move => x D. simpl. simpl in x. simpl in v0.
  simpl. case_eq (Unfold v0 x) ; first by move => a E ; rewrite E.
  move => E. rewrite E. rewrite findom_indom in D. by rewrite D.
- move => i I I'. specialize (B i).
  have C:Some (indom_app I) = n.+1 = Some (indom_app I') ; last by apply C.
  do 2 rewrite indom_app_eq. rewrite dom_create_findomF in I'.
  rewrite mem_filter in I'. rewrite create_findomF_simpl. case_eq (Unfold v0 i).
  + move => vi X. rewrite X in I'. rewrite I. have C:=findom_indom (Unfold v0) i. rewrite X in C. simpl in C.
    have C':i \in dom (Unfold w0) by rewrite A ; apply C.
    specialize (B C'). specialize (B C). have D:Some (indom_app C') = n.+1 = Some (indom_app C) by apply B. clear B.
    do 2 rewrite indom_app_eq in D. rewrite X in D. have M:=fmonotonic Unfold l.
    specialize (M i). case_eq (Unfold w0 i) ; last by move => E ; rewrite E in D.
    move => w0i E. rewrite E in D. specialize (M _ E). destruct M as [m' [M eM]]. rewrite M.
    have eeM:=eM. unfold tset_eq in eeM. simpl in eeM. apply: Mrel_trans _ D.
    by apply (proj2 (Mrefl _ _) (tset_sym eeM) n.+1).
  + move => E. case_eq (i \in dom (Unfold w1)) => EE ; first by rewrite EE.
    rewrite EE. have X:=findom_indom (Unfold w1) i. rewrite EE in X. simpl. by case: (Unfold w1 i) X.
apply Unfold_monic.
refine (@pcm_respect _ _ _ _ _ (tset_refl _) (tset_sym (UF_id _)) _).
move => i. simpl. move => f E. have ll:=fmonotonic Unfold l. specialize (ll i). clear l.
have A:=proj2 e' i. have I:i \in dom (Unfold v0) by have B:=findom_indom (Unfold v0) i ; rewrite E in B ; apply B.
have I':i \in dom (Unfold w0) by rewrite (proj1 e').
specialize (A I' I). have B:Some (indom_app I') = n.+1 = Some (indom_app I) by [].
do 2 rewrite indom_app_eq in B. clear A. rewrite create_findomF_simpl. rewrite E.
exists f. split ; last by []. rewrite E in B. case_eq (Unfold w0 i) ; last by move => E' ; rewrite E' in B.
move => w0i E'. specialize (ll _ E'). rewrite findom_indom. destruct ll as [m' [C _]]. by rewrite C.
Qed.

Lemma heap_world0 w h : heap_world 0 h w.
by [].
Qed.

Hint Resolve heap_world0.

Lemma heap_world_eq m h w w' j : (j <= m)%N -> w = m = w' -> heap_world j h w -> heap_world j h w'.
case ; first by move => h w w' j L E _ ; rewrite leqn0 in L ; rewrite (eqP L).
move => m h w w'. case ; first by [].
move => j L E. unfold heap_world. move => X k l. specialize (X k l). case: X => D X.
have E':=fnonexpansive ( Unfold) E. case: E' => D' E'.
split ; first by rewrite -> D ; apply D'.
move => i I I'. specialize (X i). have I0:i \in dom (Unfold w) by rewrite <- D.
specialize (X I0 I'). specialize (E' i I0 I). specialize (E' w).
have e:indom_app I w = m.+1 = indom_app I w' by apply (fnonexpansive ( (indom_app I))) ; apply Mmono.
have ee:indom_app I0 w = m.+1 = indom_app I w' by apply (Mrel_trans E' e). clear E' e. case: (indom_app I0 w) X ee => f Pf.
case: (indom_app I w') => g Pg. simpl. move => X Y. specialize (Y k (CValue _ (heap_cl I'))).
have l0:= leq_trans  l L. specialize (Y l0). by rewrite <- Y.
Qed.

Lemma upred_allN n R : ne_mono (@upred_allt n R).
move => n R. split.
- move => m.
  case => x0 x1. case => y0 y1. case:m ; first by [].
  move => m. case => e e'. move => k. case. case ; try done.
  move => ee C Lk. split.
  + move => A t r w j Lj. specialize (A t r). move => Lw i Li h h' v ev hv.
    simpl in e'. destruct (world_extend (Msym e') Lw) as [w' [X L']].
    specialize (A w' j Lj L' i Li). specialize (A h h' v ev).
    have hv':= heap_world_eq (leq_trans Lj Lk) X hv.
    specialize (A hv'). destruct A as [w0 [lw0 [hv0 A]]].
    destruct (world_extend (Msym X) lw0) as [w1 [E1 L1]]. exists w1. split ; first by [].
    split ; first by apply: (heap_world_eq (leq_trans (leq_subr _ _) (leq_trans Lj Lk)) E1 hv0).
    have EE:(R ((x0, r))) = m.+1 = R ((y0, r)) by apply fnonexpansive.
      specialize (EE w0). have e0:R ((y0, r)) w0 = m.+1 = R ((y0, r)) w1. apply: fnonexpansive. by apply E1.
    have e1:=Mrel_trans EE e0. clear EE e0.
    specialize (e1 (j-i) (CValue _ (proj2 (cev ev)))).
    specialize (e1 (leq_trans (leq_subr _ _) (leq_trans Lj Lk))). by rewrite <- e1.
  + move => A t r w j Lj. specialize (A t r). move => Lw i Li h h' v ev hv.
    simpl in e'. destruct (world_extend e' Lw) as [w' [X L']].
    specialize (A w' j Lj L' i Li). specialize (A h h' v ev).
    have hv':= heap_world_eq (leq_trans Lj Lk) X hv.
    specialize (A hv'). destruct A as [w0 [lw0 [hv0 A]]].
    destruct (world_extend (Msym X) lw0) as [w1 [E1 L1]]. exists w1. split ; first by [].
    split ; first by apply: (heap_world_eq (leq_trans (leq_subr _ _) (leq_trans Lj Lk)) E1 hv0).
    have EE:(R ((x0, r))) = m.+1 = R ((y0, r)) by apply fnonexpansive. specialize (EE w1).
    have e0:R (y0, r) w1 = m.+1 = R (y0, r) w0 by apply: fnonexpansive ; apply (Msym E1).
    have e1:=Mrel_trans EE e0. clear EE e0.
    specialize (e1 (j-i) (CValue _ (proj2(cev ev))) (leq_trans (leq_subr _ _) (leq_trans Lj Lk))). by rewrite e1.
- move => s w w' L. case => k v. simpl. case: v. simpl. case ; try done.
  move => v C X t f we' j Lj Lw'. specialize (X t f we' j Lj (Ole_trans L Lw')).
  move => i Li h h' v' ev hv. specialize (X i Li h h' v' ev hv).
  destruct X as [we [Lw [hv' X]]]. exists we. split ; first by []. split ; first by []. by apply X.
Qed.

Definition upred_all n (R : TVal n.+1 =-> halve_pcmType W -=> upred_pcmType (cvalue 0)) :
      (TVal n) =-> (halve_pcmType W -=> upred_pcmType (cvalue 0)) := 
  Eval hnf in mk_nemon (upred_allN R).

(*=upred_ref_down *)
Lemma upred_ref_down n 
 (R : TVal n =-> halve_pcmType W -=> upred_pcmType (cvalue 0))
 (s:TVal n) (w: halve_pcmType W) :
(*=End *)
   downclosed (fun kt => let: (k,v) := kt in
    match k,(v:cvalue O) with
     | O,CValue (LOC l) _ => True
     | S k,CValue (LOC l) _ => {P:l \in dom (Unfold w) & (indom_app P) = k.+1 = R s}
     | _,_ => False
    end).
move => n R s w. 
move => m k v L. case: m L ; first by []. move => m L. case: v. case ; try done.
move => l C [P X]. case: k L ; first by []. move => k L. exists P. by apply (Mrel_mono (ltnW L) X).
Qed.

(*=upred_reft *)
Definition upred_reft n R w : upred_pcmType (cvalue 0) :=
  exist (@downclosed _) _ (@upred_ref_down n R (fst w) (snd w)).
(*=End *)

Lemma upred_refN n R : ne_mono (@upred_reft n R).
move => n R. split.
- move => m.
  case => s w. case => s' w'. case: m ; first by []. move => m. case => e e'. move => k v. case: k ; first by []. move => k.
  case: v. case ; try done. move => l C. have X:=fnonexpansive ( Unfold) e'.
  simpl in e,e'. move => L. case: m L e e' X ; first by []. move => m L e e' X. split.
  + move => [I Y]. have Z:(Some (indom_app I)) = k.+1 = Some (R s) by apply Y.
    rewrite -> (indom_app_eq I) in Z. clear Y. rewrite (proj1 X) in I. exists I.
    have Y:(Some (indom_app I)) = k.+1 = Some (R s') ; last by apply Y.
    rewrite indom_app_eq. have e1:=fnonexpansive R e.
    have e2:=proj2 (fnonexpansive ( Unfold) e') l. simpl @snd. simpl @snd in Z, X,I.
    have I':=I. rewrite <- (proj1 X) in I'.
    specialize (e2 I' I). have e3:Some (indom_app I') = m.+1 = Some (indom_app I) by apply e2.
    do 2 rewrite indom_app_eq in e3. clear e2.
    case: (Unfold w l) e3 Z ; last by [].
    move => wl0. case: (Unfold w' l) ; last by []. move => wl0' e2 Y.
    have e4:=Mrel_mono _ e2. specialize (e4 k.+1 L). clear e2.
    apply Mrel_trans with (y:=Some wl0) ; first by apply (Msym e4). apply (Mrel_trans Y).
    apply: (fnonexpansive R). apply: (Mrel_mono _ e).
    by apply (ssrnat.ltn_trans (ltnSn k) L).
  + move => [I Y]. have Z:(Some (indom_app I)) = k.+1 = Some (R s') by apply Y.
    rewrite -> (indom_app_eq I) in Z. clear Y. simpl @snd in X,I. have I':l \in dom (Unfold w) by rewrite (proj1 X). exists I'.
    have Y:(Some (indom_app I')) = k.+1 = Some (R s) ; last by apply Y.
    rewrite indom_app_eq. have e1:=fnonexpansive R e.
    have e2:=proj2 (fnonexpansive ( Unfold) e') l. simpl @snd. simpl @snd in Z, X,I.
    specialize (e2 I' I). have e3:Some (indom_app I') = m.+1 = Some (indom_app I) by apply e2.
    do 2 rewrite indom_app_eq in e3. clear e2.
    case: (Unfold w' l) e3 Z ; last by [].
    move => wl0. case: (Unfold w l) ; last by []. move => wl0' e2 Y.
    have e4:=Mrel_mono _ e2. specialize (e4 k.+1 L). clear e2.
    apply Mrel_trans with (y:=Some wl0) ; first by apply e4. apply (Mrel_trans Y).
    apply: (fnonexpansive R). apply: (Mrel_mono _ (Msym e)).
    by apply (ssrnat.ltn_trans (ltnSn k) L).
- move => s. move => w w' Lw. case => k v. case: k ; first by []. case: v. case ; try done.
  move => l C k. move => [X Y]. simpl @snd in X,Y. simpl @fst in Y. have l2:=fmonotonic Unfold Lw. clear Lw.
  have Z: (Some (indom_app X)) = k.+1 = Some (R s) by apply Y. clear Y.
  rewrite indom_app_eq in Z. case_eq (Unfold w l) ; last by move => e ; rewrite e in Z.
  move => wl0 e. specialize (l2 l _ e). destruct l2 as [wl0' [e' e0]].
  have I:l \in dom (Unfold w') by rewrite findom_indom ; rewrite e'. exists I. simpl @fst.
  have Y:(Some (indom_app I)) = k.+1 = Some (R s) ; last by apply Y.
  rewrite (indom_app_eq). rewrite e'. rewrite e in Z.
  have e2:Some wl0' = k.+1 = Some wl0 by apply: (proj2 (Mrefl _ _) (tset_sym e0)).
  by apply (Mrel_trans e2 Z).
Qed.

(*=upred_ref *)
Definition upred_ref n
     (R : TVal n =-> halve_pcmType W -=> upred_pcmType (cvalue 0)) :
     (TVal n) =-> (halve_pcmType W -=> upred_pcmType (cvalue 0)) :=
     Eval hnf in mk_nemon (upred_refN R).
(*=End *)

(*=upred_int_down *)
Lemma upred_int_down :
  downclosed (fun kt => match snd kt : cvalue O with 
                       | (CValue (INT i) _) => True | _ => False end). (*CLEAR*) 
move => k m v l. simpl. by case: v.
Qed.

(*CLEARED*) 
Definition upred_int : upred_pcmType (cvalue 0) :=
                       exist (@downclosed _) _ upred_int_down.
(*=End *)

Lemma upred_unit_down : downclosed (fun kt => match snd kt : cvalue O with | CValue UNIT _ => True | _ => False end).
move => k m v l. simpl. by case: v.
Qed.

Definition upred_unit : upred_pcmType (cvalue 0) := exist (@downclosed _) _ upred_unit_down.

(*=upred_arrow_down *)
Lemma upred_arrow_down n
  (R0 R1: TVal n =-> halve_pcmType W -=> upred_pcmType (cvalue 0))
  (s:TVal n) (w: halve_pcmType W) : downclosed (fun kt => let: (k,v) := kt in
   match v with
   | CValue (LAM t' e) p => forall w' j (va:cvalue O), w <= w' -> (j <= k)%N -> 
              upred_fun (R0 s w') (j,va) -> IExp (R1 s) j (csubstE [:: va] e) w'
   | _ => False end).
(*=End *)
move => n R0 R1 s w.
move => m k. simpl. case. case ; try done. move => t' e C L X.
move => w' j va Lw Lj. by apply (X w' j va Lw (ssrnat.leq_trans Lj (leqW L))).
Qed.

(*=upred_arrowt *)
Definition upred_arrowt n R0 R1 s w : upred_pcmType (cvalue 0) := 
  exist (@downclosed _) _ (@upred_arrow_down n R0 R1 s w).
(*=End *)

Lemma IExp_nonexp m (f f':TV) (k:nat) (e:cexpression 0) (w w':halve_cmetricType W) : f = m = f' -> w = m = w' -> k < m -> IExp f k e w =-= IExp f' k e w'.
move => m f f' k e w w' E Ew l. unfold IExp. case: m E Ew l ; first by []. move => m E Ew l. split.
- move => X j L h h' v ev hv. specialize (X j L h h' v ev). simpl in Ew.
  have hv':=heap_world_eq _ (Msym Ew) hv. specialize (X (hv' l)). destruct X as [w0 [LL [HV Y]]].
  case: (world_extend Ew LL) => w0' [Ew' LL']. exists w0'. split ; first by [].
  split ; first by apply: (heap_world_eq (ssrnat.leq_trans (leq_subr _ _) _) Ew').
  have E':f w0 = m.+1 = f' w0' by apply Mrel_trans with (y:=f' w0) ; [by apply E | apply: fnonexpansive].
  case: (f' w0') E' => g Pg. simpl. case: (f w0) Y => g' Pg' Y.
  move => X. specialize (X (k-j) (CValue _ (proj2 (cev ev)))).
  specialize (X (leq_ltn_trans (leq_subr j k) l)). rewrite <- X. by apply Y.
- move => X j L h h' v ev hv. specialize (X j L h h' v ev).
  have hv':=heap_world_eq _ Ew hv. specialize (X (hv' l)). destruct X as [w0 [LL [HV Y]]].
  case: (world_extend (Msym Ew) LL) => w0' [Ew' LL']. exists w0'. split ; first by [].
  split ; first by apply: (heap_world_eq (ssrnat.leq_trans (leq_subr _ _) _) Ew').
  have E':f w0' = m.+1 = f' w0 by apply Mrel_trans with (y:=f' w0') ; [by apply E | apply: fnonexpansive ; apply (Msym Ew')].
  case: (f w0') E' => g Pg. simpl. case: (f' w0) Y => g' Pg' Y.
  move => X. specialize (X (k-j) (CValue _ (proj2 (cev ev)))).
  specialize (X (leq_ltn_trans (leq_subr j k) l)). rewrite -> X. by apply Y.
Qed.

Lemma upred_arrowN n R : ne_mono (fun a => @upred_arrowt n (fst R) (snd R) (fst a) (snd a)).
move => n R. split.
- case: R => R0 R1 m x y E. case: m E ; first by []. move => m E. move => k v. simpl. case: v. case ; try done.
  move => t' e C.
  move => Lk. split ; move => B w' j va lw Lj T I.
  + have E':=proj2 E. simpl in E'. case: (world_extend (Msym E') lw) => x' [E0 L0]. specialize (B x' j va L0 Lj).
    apply (proj1 (IExp_nonexp (csubstE [:: va] e) (Mrel_refl m.+1 (R1 y.1)) (Msym E0) (ssrnat.leq_trans Lj Lk))).
    have e2:(R1 x.1) = m.+1 = (R1 y.1) by apply: (fnonexpansive R1) ; apply (proj1 E).
    apply (IExp_nonexp _ e2 (Mrel_refl _ x')). by apply (leq_ltn_trans Lj Lk). apply B.
    have E1:R0 x.1 = m.+1 = R0 y.1 by apply fnonexpansive ; apply (proj1 E).
    specialize (E1 x'). have E1':=fnonexpansive ((R0 y.1)). specialize (E1' m.+1 x' w'  (Msym E0)).
    have E2:=Mrel_trans E1 E1'. clear E1 E1'. specialize (E2 j va (leq_ltn_trans Lj Lk)). by rewrite E2.
  + have E':=proj2 E. simpl in E'. case: (world_extend E' lw) => x' [E0 L0]. specialize (B x' j va L0 Lj).
    apply (proj2 (IExp_nonexp (csubstE [:: va] e) (Mrel_refl m.+1 (R1 x.1)) (E0) (ssrnat.leq_trans Lj Lk))).
    have e2:(R1 x.1) = m.+1 = (R1 y.1) by apply: (fnonexpansive R1) ; apply (proj1 E).
    apply (IExp_nonexp _ e2 (Mrel_refl _ x')). by apply (leq_ltn_trans Lj Lk). apply B.
    have E1:R0 y.1 = m.+1 = R0 x.1 by apply fnonexpansive ; apply (Msym E). specialize (E1 x').
    have E1':R0 x.1 x' = m.+1 = R0 x.1 w' by apply (fnonexpansive (R0 x.1)) ; apply (Msym E0).
    have E2:=Mrel_trans E1 E1'. clear E1 E1'. specialize (E2 j va (leq_ltn_trans Lj Lk)). by rewrite E2.
- case: R => R0 R1. move => s w w' Lw. case => k v. simpl. case: v. case ; try done. move => t0 e0 C X w1 j va Lw1 Lj.
  by apply (X w1 j va (Ole_trans Lw Lw1) Lj).
Qed.

(*=upred_arrow *)
Definition upred_arrow n 
   (R0 R1:TVal n =-> halve_pcmType W -=> upred_pcmType (cvalue 0)) :
   cmetricCatType (TVal n) (halve_pcmType W -=> upred_pcmType (cvalue 0)) :=
   Eval hnf in mk_nemon (upred_arrowN (R0,R1)).
(*=End *)

Add Parametric Morphism n : (@upred_arrow n)
with signature (@tset_eq ((metricCatType (TVal n) TV))) ==> 
               (@tset_eq ((metricCatType (TVal n) TV))) ==>
               (@tset_eq ((metricCatType (TVal n) TV)))
as upred_arrow_eq_compat.
move => x x' e y y' e'. move => s w. case => k v. simpl. case: v. case ; try done.
move => t0 ee C. split ; move => X w' j va Lw Lj ; specialize (X w' j va Lw Lj).
- move => Y. apply: (proj1 (IExp_respect _ _ _ _) (X _)) ; first by move => w0 ; apply: e'.
  specialize (e s w' (j,va)). by rewrite e.
- move => Y. apply: (proj2 (IExp_respect _ _ _ _) (X _)) ; first by move => w0 ; apply: e'.
  specialize (e s w' (j,va)). by rewrite <- e.
Qed.

Fixpoint Prod (T:Type) n : Type :=
match n with
| O => unit
| S n => (Prod T n * T)%type
end.

Definition Prod_const n T : (upred_pcmType (Prod T n) * upred_pcmType T)%CAT -> upred_pcmType (Prod T n.+1).
move => n T. case => A B.
exists (fun kt => upred_fun A (fst kt,fst (snd kt)) /\ upred_fun B (fst kt,snd (snd kt))).
move => m k. simpl. case => te t l. simpl. move => [C D].
by split ; [apply (upred_downclosed (ltnW l) C) | apply (upred_downclosed (ltnW l) D)].
Defined.

Lemma Prod_consN n T : nonexpansive (@Prod_const n T).
move => n T m. case => x y. case => x' y'. case: m ; first by [].
move => m. case => e0 e1. move => k. simpl. case => te t l. simpl.
specialize (e0 k te l). specialize (e1 k t l). rewrite e0. by rewrite e1.
Qed.

Lemma Prod_consM n T : monotonic (mk_fmet (@Prod_consN n T)).
move => n T.
case => x t. case => x' t'. case => e0 e1. case => k v. simpl. simpl in v. case: v => vt v.
specialize (e0 (k,vt)). specialize (e1 (k,v)). by move => [A B] ; split ; [apply e0 | apply e1].
Qed.

Definition Prod_cons n T : upred_pcmType (Prod T n) * upred_pcmType T =-> upred_pcmType (Prod T n.+1) :=
  Eval hnf in mk_fpcm (@Prod_consM n T).

Implicit Arguments Prod_cons [n T].

(*=IVal *)
Fixpoint IVal n (t:Ty n) : cmetricCatType (TVal n) TV :=
match t with
| TVar n J => pick J
| Int => mconst _ (pconst _ upred_int)
| Unit => mconst _ (pconst _ upred_unit)
| Mu t => FIXP << upred_mu (IVal t)
| t ** t' => (exp_fun Pcomp upred_product : metricCatType _ _) << pprod_fun_ne
                                                      << <|IVal t,IVal t'|>
| Sum t t' => (exp_fun Pcomp upred_sum : metricCatType _ _) << Pprod_fun
                                                      << <|IVal t, IVal t'|>
| All t => upred_all (IVal t)
| t --> t' => upred_arrow (IVal t) (IVal t')
| Ref t => upred_ref (IVal t)
end.
(*=End *)

(*=IEnv *)
Fixpoint IEnv n (e:TypeEnv n) :
  TVal n =-> halve_pcmType W -=> upred_pcmType (Prod (cvalue 0) (size e)) :=
match e as e0 return 
  TVal n =-> halve_pcmType W -=> upred_pcmType (Prod (cvalue 0) (size e0)) with 
| nil => mconst _ (pconst _ (upred_empty unit))
| t::te => (pcompM _ _ _ << ppair _ Prod_cons << Pprod_fun) << <| IEnv te, IVal t |>
end.
(*=End *)

(*=IStore *)
Lemma IStore_down n (Se:StoreType n) (s:TVal n) : 
  downclosed (fun kt => forall l t, Se l = Some t ->
                        upred_fun (IVal (Ref t) s (snd kt)) (fst kt, cLOC _ l)). (*CLEAR*)
move => n Se s.
move => m k w Lk. move => X.
move => l t E. specialize (X l t E).
by apply (upred_downclosed (ltnW Lk) X).
Qed.
(*CLEARED*)
Definition IStore n (Se:StoreType n) (s:TVal n) : upred_pcmType W :=
                              exist (@downclosed _) _ (@IStore_down n Se s).
(*=End *)

Fixpoint Prod_subst T n : Prod T n -> seq T :=
match n as n0 return Prod T n0 -> seq T with 
| O => fun _ => nil
| S n => fun P => snd P :: (Prod_subst (fst P))
end.

(*=VRel *)
Definition VRel n (E:TypeEnv n) (Se:StoreType n) (v:Value n) (t:Ty n) := 
  forall k (s:TVal n) (ts:Prod (Ty 0) n) g w,
    upred_fun (IEnv E s w) (k,g) -> upred_fun (IStore Se s) (k,w) ->
 upred_fun (IVal t s w) (k, csubstV (Prod_subst g) (vtsubst (Prod_subst ts) v)).
Definition ERel n (E:TypeEnv n) (Se:StoreType n) (e:Exp n) (t:Ty n) :=
  forall k (s:TVal n) (ts:Prod (Ty 0) n) g w,
     upred_fun (IEnv E s w) (k,g) -> upred_fun (IStore Se s) (k,w) ->
     IExp (IVal t s) k (csubstE (Prod_subst g) (etsubst (Prod_subst ts) e)) w.
(*=End *)

Lemma FT_var n m (E:TypeEnv n) s w k g t : nth_error E m = Some t -> upred_fun (IEnv E s w) (k, g) ->
   upred_fun (IVal t s w) (k,nth (cUNIT _) (Prod_subst g) m).
Proof.
move => n m E. elim: E m  ;first by [].
move => t E IH m s w k g t'. case: m.
- simpl. case => e. rewrite <- e. clear e t'. by move => [A B].
- move => m. simpl. move => e. specialize (IH m s w k g.1 _ e).
  move => [A B]. by apply (IH A).
Qed.

Lemma IVal_shift n (t:Ty n) (s:TVal n) (s':TVal n.+1) k :
   (forall i, k <= i -> forall (P':1 + i < 1 + n) (P:i < n), (pick P s) = (pick P' s')) ->
   (forall i, i < k -> forall (P':i < 1 + n) (P:i < n), (pick P' s') = (pick P s)) ->
   IVal (tshiftL k 1 t) s' =-= IVal t s.
move => n t. elim: n / t.
- move => n i L s s' k X Y w.
  have L':=L. rewrite <- (ltn_add2l 1 i n) in L'.
  case: (leqP k i) => Lk.
  + rewrite (tshiftL_var L L' Lk). simpl.
    apply tset_trans with (y:=(pick L' s') w) ; first by [].
    apply tset_trans with (y:=(pick L s) w) ; last by []. by rewrite (X i Lk L' L).
  + have Li := (ltn_addl 1 L).
    rewrite (tshiftL_var2 L Li Lk). apply tset_trans with (y:=(pick Li s') w) ; first by [].
    apply tset_trans with (y:=(pick L s) w) ; last by [].
    by rewrite (Y _ Lk Li L).
- move => n s s' w X Y. by rewrite tshiftL_int.
- move => n s s' w X Y. by rewrite tshiftL_unit.
- move => n t0 IH0 t1 IH1 s s' k w X Y. simpl. rewrite tshiftL_pair.
  specialize (IH0 s s' k w X Y). specialize (IH1 s s' k w X Y). simpl.
  case => m v. simpl. case: v. case ; try done. move => v0 v1 C.
  rewrite IH0. by rewrite IH1.
- move => n t0 IH0 t1 IH1 s s' k w X Y. simpl. rewrite tshiftL_sum.
  specialize (IH0 s s' k w X Y). specialize (IH1 s s' k w X Y). simpl.
  case => m v. simpl. by case: v ; case.
- move => n t IH s s' k X Y w. simpl. have e:(1 + n.+1)%N = (1+n).+1 by rewrite addnS. rewrite (tshiftL_mu _ e).
  rewrite (eq_irrelevance e (refl_equal _)). simpl.
  apply tset_trans with (y:=FIXP (upred_mu (IVal (tshiftL k.+1 1 t)) s') w) ; first by [].
  apply tset_trans with (y:=FIXP (upred_mu (IVal t) s) w) ; last by [].
  have ee:upred_mu (IVal (tshiftL k.+1 1 t)) s' =-= upred_mu (IVal t) s ; last by
    apply (frespect ( (FIXP )) ee).
  move => R w'. case => j v. simpl. case: j ; first by case: v.
  move => j. case:v. case ; try done. move => t' v C. specialize (IH (s, R) (s', R) k.+1).
  apply IH.
  + case ; first by []. move => i L P' P ; by apply: X ; apply L.
  + move => i L P' P. case: i L P P' ; first by []. move => i L P P'. specialize (Y i L P' P). by apply: Y.
- move => n t IH s s' k X Y w. simpl. have e:(1 + n.+1)%N = (1+n).+1 by rewrite addnS. rewrite (tshiftL_all _ e).
  rewrite (eq_irrelevance e (refl_equal _)). simpl.
  case => j v. simpl. case: v. simpl. case ; try done. move => v C. split.
  + move => A t1 r w' i Li Lw. specialize (IH (s, r) (s', r) k.+1).
    specialize (A t1 r w' i Li Lw). refine (proj1 (IExp_respect _ _ _ _) A).
    clear i Li w' A Lw. move => w'. apply: IH.
    * case ; first by []. move => i L P' P ; by apply: X ; apply L.
    * move => i L P' P. case: i L P P' ; first by []. move => i L P P'. specialize (Y i L P' P). by apply: Y.
  + move => A t1 r w' i Li Lw. specialize (IH (s, r) (s', r) k.+1).
    specialize (A t1 r w' i Li Lw). refine (proj2 (IExp_respect _ _ _ _) A).
    clear i Li w' A Lw. move => w'. apply: IH.
    * case ; first by []. move => i L P' P ; by apply: X ; apply L.
    * move => i L P' P. case: i L P P' ; first by []. move => i L P P'. specialize (Y i L P' P). by apply: Y.
- move => n t0 IH0 t1 IH1 s s' k X Y w. specialize (IH0 s s'). specialize (IH1 s s').
  rewrite tshiftL_arrow. simpl. case => j v. simpl. case: v. case ; try done.
  move => tx e0 C. split ; move => A w' j0 va Lw Lj ; specialize (A w' j0 va Lw Lj).
  + move => B.
    refine (proj1 (IExp_respect _ _ _ _) (A _)). move => w''. specialize (IH0 _ X Y w''). specialize (IH1 _ X Y w'').
    apply IH1. specialize (IH0 _ X Y w'). clear IH1. specialize (IH0 (j0,va)). apply (proj2 IH0). apply B.
  + move => B.
    refine (proj1 (IExp_respect _ _ _ _) (A _)). move => w''.  specialize (IH0 _ X Y w''). specialize (IH1 _ X Y w'').
    apply (tset_sym IH1). specialize (IH0 _ X Y w'). clear IH1. specialize (IH0 (j0,va)). apply (proj1 IH0). apply B.
- move => n t IH s s' k X Y w. rewrite tshiftL_ref. simpl. specialize (IH s s' k).
  case => j v. simpl. case: j ; first by []. move => j. case: v. case ; try done.
  move => l C. split ; move => [P Z] ; exists P ; move => w' i v Li ; specialize (Z w' i v Li) ; rewrite Z ;
    specialize (IH X Y w' (i,v)) ; by rewrite IH.
Qed.

Lemma IEnv_shift n (E:TypeEnv n) s w k x g e : upred_fun (IEnv E s w) (k, g) ->
  upred_fun (IEnv (map (@tshiftL 0 1 _) E) (s, x) w) (k, (eq_rect _ (Prod (cvalue 0)) g _ e)).
move => n. elim ; first by [].
move => t E IH s w k x g. simpl. move => e X. specialize (IH s w k x). simpl in g.
have e':(size E) = (size (map (@tshiftL 0 1 _) E)) by auto.
specialize (IH (fst g) e' (proj1 X)).
have ee:eq_rect (size E) (Prod (cvalue 0)) g.1 (size (map (@tshiftL 0 1 _) E)) e' = (eq_rect (size E).+1 (Prod (cvalue 0)) g (size (map (@tshiftL 0 1 _) E)).+1 e).1.
  clear X IH. case: g => g a. simpl. move: e. generalize e'. rewrite <- e'. clear e'. move => e e'.
  rewrite (eq_irrelevance e (refl_equal _)). by rewrite (eq_irrelevance e' (refl_equal _)).
rewrite ee in IH. split ; first by apply IH. clear ee IH. case: g X. simpl. move => g v X.
have ee: (eq_rect (size E).+1 (Prod (cvalue 0)) (g, v) (size (map (@tshiftL 0 1 _) E)).+1 e).2 = v.
move: e. rewrite <- e'. simpl. move => e. by rewrite (eq_irrelevance e (refl_equal _)).
rewrite ee.
have AA:=(@IVal_shift _ t s (s,x) 0 _ _ w (k,v)). rewrite AA ; first by apply (proj2 X).
- move => i L P' P. simpl. by rewrite (eq_irrelevance P P').
- by [].
Qed.

Lemma heap_world_down j k h w : j <= k -> heap_world k h w -> heap_world j h w.
move => j k h w L X i Li. specialize (X i (ssrnat.leq_trans Li L)). split ; case: X ; move => X Y ; first by apply X.
move => l I I'. specialize (Y l I I'). by apply Y.
Qed.

Lemma IStore_upclosed n t (s:TVal n) j w w' : w <= w' -> upred_fun (IStore t s) (j,w) -> upred_fun (IStore t s) (j,w').
move => n t s j w w' L. unfold IStore. simpl. move => X l t' E. specialize (X l t' E).
case: j X ; first by []. move => j [P X]. have ll:=fmonotonic Unfold L. clear L.
have D:l \in dom (Unfold w'). rewrite findom_indom. clear X. rewrite findom_indom in P.
  case_eq (Unfold w l) => wl ; last by rewrite wl in P.
  move => E'. specialize (ll _ _ E'). destruct ll as [wl' [E0 _]]. by rewrite E0.
exists D. move => x k t0 L'. specialize (X x k t0 L'). rewrite <- X. clear X.
specialize (ll l). case_eq (Unfold w l). move => m E'. specialize (ll _ E').
destruct ll as [m' [E0 e0]]. have aa:Some (indom_app D) = Some (m'). by rewrite indom_app_eq.
case: aa => aa. rewrite aa. clear aa. have aa:Some (indom_app P) = Some m by rewrite indom_app_eq.
case: aa => aa. rewrite aa. clear aa. have EE:=e0 x (k,t0). by rewrite EE.
move => E'. have F:False ; last by []. rewrite findom_indom in P. by rewrite E' in P.
Qed.

Lemma IVal_upclosed n (t:Ty n) s w w' k v : w <= w' -> upred_fun (IVal t s w) (k,v) -> upred_fun (IVal t s w') (k,v).
move => n t s w w' k v Lw. apply (fmonotonic (IVal t s) Lw (k,v)).
Qed.

Lemma IEnv_upclosed n E (s:TVal n) k v w w' : w <= w' -> upred_fun (IEnv E s w) (k,v) -> upred_fun (IEnv E s w') (k,v).
move => n E. elim: E ; first by [].
move => t E IH s k. simpl. case => ve v w w' Lw. simpl. move => [A B]. specialize (IH s k ve w w' Lw).
split ; first by apply IH. by apply (IVal_upclosed Lw B).
Qed.

Lemma IExp_eq f k w e e' : e = e' -> IExp f k e w -> IExp f k e' w.
move => f k w e e' E. by rewrite E.
Qed.

Lemma world_update (w:W) t l : l \notin dom (Unfold w) -> w <= (Fold (updMap l t (Unfold w))).
move => w. move => f l X.
apply Unfold_monic. have ee:=UF_id (updMap l f (Unfold w)).
refine (pcm_respect (tset_refl _) (tset_sym ee) _). clear ee. simpl.
move => l0 m e. case_eq (l0 == l) => A.
- rewrite <-(eqP A) in X. rewrite findom_indom in X. by rewrite e in X.
- have B:(l0 != l) by rewrite A. clear A.
  exists m. rewrite updMap_simpl2 ; last by apply B. by rewrite e.
Qed.

Lemma csubst_var m n (g:Prod (cvalue O) n) : csubstV (Prod_subst g) (VAR m) = nth (cUNIT _) (Prod_subst g) m.
move => m n g. unfold csubstV. have A:=(closedV_sub (VAR m) (map_closed (Prod_subst g))).
rewrite (eq_irrelevance (closedV_sub (VAR m) (map_closed (Prod_subst g))) A). move: A. simpl.
elim: n m g. simpl.
- case ; simpl.
  + move => _ A.  by rewrite (eq_irrelevance A (refl_equal _)).
  + move => _ _ A.  by rewrite (eq_irrelevance A (refl_equal _)).
- move => n IH m. simpl. case => g t. simpl. case: m.
  + move => A. simpl. simpl in A. case: t A. simpl. move => v C a. by rewrite (eq_irrelevance a C).
  + move => m. simpl. move => A. by apply (IH _ g A).
Qed.

Lemma upred_fun_imp k n (X:upred_pcmType (cvalue n)) (a:Value n) (A B:closedV a) : upred_fun X (k,CValue _ A) -> upred_fun X (k,CValue _ B).
move => k n X a A B Y. have e:CValue _ A = CValue _ B by apply CValue_eq.
rewrite <- e. by apply Y.
Qed.

Lemma heap_eq (h h':cheap) : heap h = heap h' -> h = h'.
case => h Ph. case => h' Ph'. simpl. move => e. move: Ph Ph'. rewrite e.
move => P P'. by rewrite (eq_irrelevance P P').
Qed.

(*=IValSubst *)
Lemma IVal_subst n (t:Ty n) s m s' (a:seq (Ty m)) :
     (forall i (P:i < n), pick P s =-= (IVal (nth Unit a i) s')) -> 
                          IVal t s =-= IVal (tsubst a t) s'.
(*=End *)
move => n t. elim: n / t => n.
- move => i P s m s' a X. simpl. specialize (X _ P). by apply X.
- by [].
- by [].
- move => t0 IH0 t1 IH1 s m s' a X. simpl. move => w. simpl.
  apply upred_product_eq_compat. split ; first by simpl ; apply (IH0 _ _ _ _ X). simpl. by apply: IH1.
- move => t0 IH0 t1 IH1 s m s' a X. simpl. move => w. simpl.
  apply upred_sum_eq_compat. split ; first by simpl ; apply (IH0 _ _ _ _ X). simpl. by apply: IH1.
- move => t IH s m s' a X. simpl. apply: frespect.
  move => f x. simpl.
  case => k v. simpl. case: v. case ; case: k ; try done. move => k t' v C.
  specialize (IH (s, f) m.+1 (s', f) (TVar (ltn0Sn m) :: map (@tshiftL 0 1 _) a)).
  apply: IH.
  case ; first by []. move => j P. simpl. specialize (X j P). apply (tset_trans X).
  case_eq (j < size a) => A.
  + have AA:= (nth_map (@Unit _) (@Unit _) (@tshiftL 0 1 _) A). rewrite (f_equal (@IVal _) AA).
    apply: (tset_sym (IVal_shift _ _ _)) ; last by []. move => i L P0 P1. simpl.
    by rewrite (eq_irrelevance P1 P0).
  + rewrite ltnNge in A. have AA:=negbFE A. clear A. rewrite (nth_default Unit AA).
    rewrite (nth_default Unit) ; last by rewrite size_map. by [].
- move => t IH s m s' a X. simpl. move => w. simpl.
  case => k. case. case ; try done. move => e C. simpl. split => A t' f w' j Lj Lw.
  specialize (A t' f w' j Lj Lw). specialize (IH (s, f) m.+1 (s', f)).
  specialize (IH (TVar (ltn0Sn m) :: map (@tshiftL 0 1 _) a)).
  apply: proj1 (IExp_respect _ _ _ (IH _)) A. case ; first by []. simpl.
  move => i P. apply (tset_trans (X i P)).
  case_eq (i < size a) => A.
  + have AA:= (nth_map (@Unit _) (@Unit _) (@tshiftL 0 1 _) A). rewrite (f_equal (@IVal _) AA).
    apply: (tset_sym (IVal_shift _ _ _)) ; last by []. move => i' L P0 P1. simpl.
    by rewrite (eq_irrelevance P1 P0).
  + rewrite ltnNge in A. have AA:=negbFE A. clear A. rewrite (nth_default Unit AA).
    rewrite (nth_default Unit) ; last by rewrite size_map. by [].
  specialize (A t' f w' j Lj Lw). specialize (IH (s, f) m.+1 (s', f)).
  specialize (IH (TVar (ltn0Sn m) :: map (@tshiftL 0 1 _) a)).
  apply: proj2 (IExp_respect _ _ _ (IH _)) A. case ; first by []. simpl.
  move => i P. apply (tset_trans (X i P)).
  case_eq (i < size a) => A.
  + have AA:= (nth_map (@Unit _) (@Unit _) (@tshiftL 0 1 _) A). rewrite (f_equal (@IVal _) AA).
    apply: (tset_sym (IVal_shift _ _ _)) ; last by []. move => i' L P0 P1. simpl.
    by rewrite (eq_irrelevance P1 P0).
  + rewrite ltnNge in A. have AA:=negbFE A. clear A. rewrite (nth_default Unit AA).
    rewrite (nth_default Unit) ; last by rewrite size_map. by [].
- move => t0 IH0 t1 IH1 s m s' a X. simpl. move=> w. simpl. case => k v. simpl. case: v. case ; try done.
  move => t e C. split => Z w' j va Lw Lj Y.
  + specialize (Z w' j va Lw Lj). specialize (IH0 s _ s' a X w' (j,va)).
    have Z':=Z (proj2 IH0 Y). move => i Li h h' v ev hv.
    specialize (Z' i Li h h' _ ev hv). destruct Z' as [w0 [Lw0 [hv0 Z']]]. exists w0. split ; first by [].
    split ; first by []. specialize (IH1 s _ s' a X w0 (j-i,CValue v (proj2 (cev ev)))). by apply (proj1 IH1 Z').
  + specialize (Z w' j va Lw Lj). specialize (IH0 s _ s' a X w' (j,va)).
    have Z':=Z (proj1 IH0 Y). move => i Li h h' v ev hv.
    specialize (Z' i Li h h' _ ev hv). destruct Z' as [w0 [Lw0 [hv0 Z']]]. exists w0. split ; first by [].
    split ; first by []. specialize (IH1 s _ s' a X w0 (j-i,CValue v (proj2 (cev ev)))). by apply (proj2 IH1 Z').
- move => t IH s m s' a X. simpl. move => w. simpl. case => k. case. case ; try done. move => j C.
  simpl. case: k ; first by []. move => k. split ; case => A B ; exists A => x i v Li ; specialize (B x i v Li).
  + rewrite B. apply: IH. by apply X.
  +  apply iff_sym. rewrite B. apply: IH. by apply X.
Qed.

(*=Fundamental *)
Lemma FT i E S t : (forall v, i |- E | S |v- v ::: t -> VRel E S v t) /\
                     (forall e, i |- E | S |e- e ::: t -> ERel E S e t).
(*=End *)
apply (@Typing_ind) => i E S t.
- move => m e. move => k s ts g w. move => X Y. simpl. rewrite csubst_var. simpl. by apply (FT_var e).
- move => t' l e e'. rewrite e'. clear e' t. move => k s ts g w. case: k ; first by move => Ig Is. move => k Ig Is.
  simpl. simpl in Is. specialize (Is l t' e). case: Is => Dl Is. exists Dl. move => w' j t Lj.
  specialize (Is w' j t Lj). by rewrite Is.
- move => n e. rewrite e. clear t e. by move => j s g w X Y.
- move => e t' e'. rewrite e'. clear t e'. move => X Y k s ts g w. move => A B. move => t r w' j Lj. simpl. move => Lw.
  specialize (Y j (s,r) (ts,t)). have ee:(size E) = (size (map (@tshiftL 0 1 _) E)) by rewrite size_map.
  specialize (Y (eq_rect _ (Prod (cvalue 0)) g _ ee) w').
  have Y':=Y (IEnv_shift _ _ (upred_downclosed Lj _)). clear Y.
  specialize (Y' (IEnv_upclosed Lw A)).
  have C:upred_fun (IStore (post_compt (@tshiftL 0 1 _) S) (s, r)) (j, w').
    apply (upred_downclosed Lj). apply: (IStore_upclosed Lw _). clear Y' Lj j A Lw w' X e.
    move => l t0 D. specialize (B l). rewrite post_comp_simpl in D. case_eq (S l) ; last by move => AA ; rewrite AA in D.
    move => Sl e'. specialize (B _ e'). case: k B ; first by [].
    move => k. simpl. case => Iw B. exists Iw. move => x j v Lj. specialize (B x j v Lj). rewrite B. clear B.
    rewrite e' in D. simpl in D. case: D => D. rewrite <- D. clear t0 D.
    have A:=@IVal_shift _ Sl s (s,r) 0 _ _ x (j,v). rewrite A ; first by [].
    + clear. move => j _ P' P. simpl. by rewrite (eq_irrelevance P P').
    + by [].
  specialize (Y' C). clear C. apply: (IExp_eq _ Y'). clear Y'. clear. unfold csubstE.
  apply CExp_eq. simpl.
  rewrite <- etsubst_tsubst. rewrite map_map. rewrite etsubst_map. simpl. rewrite map_map.
  rewrite map_map. have e1:map (fun x : Ty 0 => tsubst [:: t] (tshiftL 0 1 x)) =1 map id.
    apply eq_map. move => x. simpl. have AA:= @tsubst_shiftLW 1 0 x 0 0 [:: t] [::] (refl_equal _) (refl_equal _).
    rewrite AA. by rewrite tsubst_id.
  rewrite e1. clear e1. rewrite map_id. move: ee. rewrite size_map. move => ee.
  rewrite (eq_irrelevance ee (refl_equal _)). simpl. f_equal.
  apply eq_map. move => x. simpl.
  clear. rewrite vtsubst_map. simpl. by rewrite vtsubst_id.
- move => t0 t1 b e. rewrite e. clear t e. move => Db IH. move => k s ts g w Ig Is. simpl.
  move => w' j va Lw Lj T X. specialize (IH j s ts (g,va) w').
  have AA:upred_fun (IEnv (t0 :: E) s w') (j, (g, va)). split ; last by [].
    simpl. apply (IEnv_upclosed Lw). by apply (upred_downclosed Lj).
  specialize (IH AA). clear AA. have Is':=upred_downclosed Lj (IStore_upclosed Lw Is).
  specialize (IH Is'). clear Is'. apply: (IExp_eq _ IH). apply CExp_eq.
  rewrite substE_map. simpl. rewrite map_map. simpl. f_equal. f_equal.
  rewrite map_map. apply eq_map. move => x. simpl.
  have AA:= @substV_shiftW 1 0 x 0 [:: (cval va)] [::] (refl_equal _) (refl_equal _).
  rewrite AA. by rewrite (substV_cid).
- move => e. by rewrite e.
- move => t0 t1 e0 e1 e. rewrite e. clear t e. move => _ IH0 _ IH1. move => k s ts g w Ig Is. simpl.
  specialize (IH0 k s ts g w Ig Is). specialize (IH1 k s ts g w Ig Is). split.
  + by apply (upred_fun_imp _ IH0).
  + by apply (upred_fun_imp _ IH1).
- move => t0 t1 e _ IH0 e'. rewrite e'. clear t e'. move => k s ts g w Ig Is.
  specialize (IH0 k s ts g w Ig Is). simpl. apply (upred_fun_imp _ IH0).
- move => t0 t1 e _ IH0 e'. rewrite e'. clear t e'. move => k s ts g w Ig Is. simpl.
  by apply (upred_fun_imp _ (IH0 k s ts g w Ig Is)).
- move => t' e _ IH e'. rewrite e'. clear t e'. move => k s ts g w Ig Is. simpl IVal.
  have ee:=FIXP_fp (upred_mu (IVal t') s).
  specialize (ee w (k, csubstV (Prod_subst g) (vtsubst (Prod_subst ts) (FOLD t' e)))). apply (proj2 ee). clear ee.
  case: k Ig Is ; first by []. move => k Ig Is. simpl.
  specialize (IH k.+1 s ts g w Ig Is). have A:=proj2 (IVal_subst _ _ _ _) IH.
  specialize (A (s,FIXP (upred_mu (IVal t') s))).
  unfold csubstV in A.
  rewrite (CValue_eq _ (closedV_sub (vtsubst (Prod_subst ts) e) (map_closed (Prod_subst g)))
            (refl_equal (substV (map (@cval _) (Prod_subst g)) (vtsubst (Prod_subst ts) e)))).
  apply: (upred_downclosed (leqW (leqnn _)) (A _)).
  case ; first by []. move => j P. simpl. rewrite (@nth_idsub i O j P).
  simpl. by rewrite <- (eq_irrelevance P (@ltn_addl j i O P)).
- move => v _ IH k s ts g w Ig Is. simpl. specialize (IH k s ts g w Ig Is). simpl.
  move => j Lj h h' v0 ev. inversion ev. clear h0 H0. clear v1 H1.
  have ee:h = h' by apply heap_eq. clear H4.
  move: ev. rewrite <- ee. move => ev.
  clear h' ee. move: ev. rewrite <- H2. clear v0 H2. rewrite <- H. clear Lj H j.
  move => ev hv. exists w. split ; first by []. rewrite subn0. split ; first by [].
  by apply (upred_fun_imp _ IH).
- move => e0 e1 t' _ IH0 _ IH1. move => k s ts g w Ig Is.
  move => j Lj h h' v ev. inversion ev. clear h0 H0. clear v1 H3. clear e2 H1 e3 H2 H4.
  move => hv. have Ln0 := leq_addr n1 n0. rewrite H in Ln0.
  specialize (IH0 k s ts g w Ig Is n0 (leq_trans Ln0 Lj) h).
  destruct (ev_closed X (@closedE_sub _ (etsubst (Prod_subst ts) e1) (map (@cval _) (Prod_subst g)) nil (map_cvalP _)) (cheapP h)) as [Ch1 Cv0].
  specialize (IH0 (CHeap Ch1) _ X hv).
  destruct IH0 as [w1 [Lw [hv0 IH0]]]. specialize (IH1 (k-n0) s ts (g,CValue _ Cv0) w1).
  have A:upred_fun (IEnv (t' :: E) s w1) (k - n0, (g, CValue _ Cv0)).
  split ; simpl ; last by  apply (upred_fun_imp _ IH0).
    by apply: (IEnv_upclosed Lw) ; apply: (upred_downclosed _ Ig) ; apply leq_subr.
  specialize (IH1 A).
  have B:upred_fun (IStore S s) (k - n0, w1) by apply (IStore_upclosed Lw) ; apply: (upred_downclosed _ Is) ; apply leq_subr.
  specialize (IH1 B n1).
  have Ln1:(n1 <= k - n0)%N. have Ln11:=leq_addl n0 n1. rewrite H in Ln11. rewrite <- (subnKC Ln0) in H.
  have aa:= eqn_addl n0 n1 (j - n0). rewrite H in aa. rewrite eq_refl in aa. rewrite (eqP (sym_eq aa)).
    by apply leq_sub2r.
  specialize (IH1 Ln1 (CHeap Ch1) h'). rewrite substE_map in X0. simpl in X0. do 2 rewrite map_map in X0.
  unfold csubstE in IH1. simpl in IH1.
  have ee:map (fun x : cvalue 0 => substV [:: v0] (shiftV 0 1 x)) (Prod_subst g) = map (@cval _) (Prod_subst g).
  apply eq_map.
    move => x. simpl. rewrite (@substV_shiftW _ _ x _ [::v0] [::]) ; [idtac | by [] | by []]. by apply substV_cid.
  rewrite ee in X0. clear ee. specialize (IH1 _ X0 hv0). destruct IH1 as [wr [Lwr [hvr IH1]]].
  exists wr. split ; first by apply (Ole_trans Lw Lwr). rewrite subn_sub in IH1. rewrite H in IH1.
  split ; last by apply (upred_fun_imp _ IH1).
  rewrite subn_sub in hvr. rewrite H in hvr. by apply hvr.
- move => t' v _ IH k s ts g w Ig Is. move => j Lj h h' v' ev. inversion ev. clear h0 H0.
  specialize (IH k s ts g w Ig Is). move: ev. rewrite <- H. clear j H Lj. rewrite H2 in H1. clear v0 H2.
  have ee:h = h' by apply heap_eq. clear H4.
  rewrite <- ee. clear h' ee. move => ev hv.
  exists w. split ; first by []. rewrite subn0. split ; first by [].
  have E':=(closedV_sub (vtsubst (Prod_subst ts) v) (map_closed (Prod_subst g))). simpl in IH.
  rewrite (eq_irrelevance (closedV_sub (vtsubst (Prod_subst ts) v) (map_closed (Prod_subst g))) E') in IH.
  move: E' IH. rewrite <- H1. simpl. move => E'. move => IH1.
  by apply (upred_fun_imp _ (proj1 IH1)).
- move => t' v _ IH k s ts g w Ig Is. move => j Lj h h' v' ev. inversion ev. clear h0 H0.
  specialize (IH k s ts g w Ig Is). move: ev. rewrite <- H. clear j H Lj. rewrite H2 in H1. clear v1 H2.
  have ee:h = h' by apply heap_eq. clear H4.
  rewrite <- ee. clear h' ee. move => ev hv.
  exists w. split ; first by []. rewrite subn0. split ; first by [].
  have E':=(closedV_sub (vtsubst (Prod_subst ts) v) (map_closed (Prod_subst g))). simpl in IH.
  rewrite (eq_irrelevance (closedV_sub (vtsubst (Prod_subst ts) v) (map_closed (Prod_subst g))) E') in IH.
  move: E' IH. rewrite <- H1. simpl. move => E'. move => IH1.
  by apply (upred_fun_imp _ (proj2 IH1)).
- move => op v e. rewrite e. clear t e. move => _ IH k s ts g w Ig Is. move => j Lj h h' v' ev. inversion ev. clear h0 H0.
  clear op0 H1. move: ev. rewrite <- H3. rewrite <- H5. have ee:h = h' by apply heap_eq. rewrite <- ee. clear H3 h' ee H5.
  simpl. move => ev hv. exists w. rewrite <- H. split ; first by []. rewrite subn0. split ; first by []. by [].
- move => t' v _ IH e. rewrite e. clear t e. move => k s ts g w Ig Is. simpl.
  move => j Lj h h' v' ev hv. inversion ev. clear h0 H0. rewrite H2 in H1. clear v0 H2. move: ev. rewrite <- H4.
  have ee:h = h' by apply heap_eq. rewrite <- ee.
  clear h' H4 ee. simpl. move => ev.
  specialize (IH k s ts g w Ig Is). exists w. split ; first by []. split ; first apply: (heap_world_down _ hv).
    by apply: (leq_subr _). have A:=(closedV_sub (vtsubst (Prod_subst ts) v) (map_closed (Prod_subst g))).
  simpl @IVal in IH. simpl in IH.
  have IH' := proj1 (FIXP_fp (upred_mu (IVal t') s) w (k, csubstV (Prod_subst g) (vtsubst (Prod_subst ts) v))) IH. clear IH. rewrite <- H in Lj.
  simpl in IH'. case: k Ig Is Lj hv IH' ; first by [].
  move => k Ig Is _ hv IH.
  rewrite (eq_irrelevance (closedV_sub (vtsubst (Prod_subst ts) v) (map_closed (Prod_subst g))) A) in IH. move: A IH.
  rewrite <- H1. move => A IH. move: ev. rewrite <- H. clear j H. move => ev. rewrite subSS. rewrite subn0.
  simpl in A.
  apply (@upred_fun_imp _ _ _ _ A).
  apply: proj1 (IVal_subst t' _ w (k,CValue v' A)) IH.
  case; first by []. move => j P. simpl. rewrite (@nth_idsub i O j P). simpl.
  by rewrite (eq_irrelevance (@ltn_addl j i O P) P).
- move => v t' _ IH e. rewrite e. clear e t. move => k s ts g w Ig Is. simpl. move => j Lj h h' v' ev hv.
  inversion ev. move: ev. rewrite <- H3. move: Lj. rewrite <- H0. clear H0 j h0 v' H3 H2. rewrite <- H1.
  move => L. case: k L Ig Is hv ; first by []. move => k _ Ig Is hv. simpl.
  move => _.
  exists (Fold (updMap l (IVal t' s) (Unfold w))).
  have Lw:(w <= Fold (updMap l (IVal t' s) (Unfold w))).
    apply: world_update. specialize (hv 0 (ltn0Sn _)).
     rewrite (proj1 hv) in H4. by apply H4.
  split ; first by apply Lw.
  have ufe:forall x, (Unfold (Fold x)) =-= x by apply UF_id.
  have fue:forall x, (Fold (Unfold x)) =-= x by apply FU_id.
  split.
  + move => m Lm. split.
    * rewrite (proj1 (ufe _)). rewrite <- H1.
      refine (eqP (dom_upd _ _ _ _)). have aa:=proj1 (hv m (ssrnat.ltn_trans Lm _)).
        clear Ig Is. case: k Lm hv aa ; first by []. move => k Lm _ aa. rewrite subSS in aa. rewrite subn0 in aa.
        specialize (aa(ltnSn _)). by rewrite aa.
    * move => l1 I I'.
      have ee:Some (indom_app I) =
               ((Unfold (Fold (updMap l (IVal t' s) (Unfold w)))) l1).
      by rewrite (indom_app_eq I).
      case_eq (Unfold (Fold (updMap l (IVal t' s) (Unfold w))) l1) ; last by 
        move => F ; rewrite F in ee.
      move => fl0 E'. rewrite E' in ee. simpl in ee. have e0:=ee. rewrite indom_app_eq in ee.
      case: e0 => e0. rewrite e0. clear e0 I. clear ee.
      case: k Lm hv Ig Is ; first by []. move => k Lm hv Ig Is. rewrite subSS in Lm. rewrite subn0 in Lm.
      specialize (hv m (ssrnat.ltn_trans Lm (ltnSn _))).  destruct hv as [Dhv hv].
      specialize (hv l1).
      case_eq (updMap l (IVal t' s) (Unfold w) l1).
      - move => f E0. specialize (ufe (updMap l (IVal t' s) (Unfold w))).
        have uf:=proj2 ufe l1. rewrite E0 in uf. simpl in uf. simpl in E'.
        have ee:Some fl0 =-= Some f. rewrite <- uf. by rewrite E'. clear uf.
        case_eq (l == l1) => el. rewrite (eqP el) in  E0. rewrite updMap_simpl in E0. case: E0 => E0.
        + rewrite E0. specialize (IH m s ts g (Fold (updMap l f (Unfold w)))). rewrite E0 in Lw.
          have ll:(m <= k.+2)%N by apply (leqW (ltnW Lm)).
          specialize (IH (upred_downclosed ll (IEnv_upclosed Lw Ig)) (upred_downclosed ll (IStore_upclosed Lw Is))).
            have A:=(heap_cl I'). rewrite (eq_irrelevance (heap_cl I') A). move: A.
          have ex:Some (indom_app I') = Some v0. rewrite indom_app_eq. rewrite <- (eqP el). rewrite <- H1.
            rewrite updMap_simpl. by rewrite H.
          case: ex => ex. rewrite ex. rewrite H.
          rewrite E0 in IH. simpl in ee.
          specialize (ee (Fold (updMap l f (Unfold w)))). move => A.
          specialize (ee (m,CValue _ A)).
          apply (proj2 ee). apply (upred_fun_imp _ IH).
        + rewrite updMap_simpl2 in E0.
          have D0:l1 \in dom (Unfold w) by rewrite findom_indom ; rewrite E0.
          specialize (hv D0). have D1:=D0. rewrite <- Dhv in D1. specialize (hv D1).
          have ea: CValue _ (heap_cl I') = CValue _ (heap_cl D1). apply CValue_eq.
          have ea: Some (indom_app I') = Some (indom_app D1).
           do 2 rewrite indom_app_eq. rewrite <- H1. rewrite updMap_simpl2.
            by []. apply negbT. by apply negbF_imp => e0 ; rewrite (eqP e0) in el ; rewrite eq_refl in el.
            by case: ea.
          rewrite ea.
          clear I' ea.
          apply (fmonotonic fl0 Lw). specialize (ee w). simpl in ee. specialize (ee (m,CValue _ (heap_cl D1))).
          apply (proj2 ee). have ea:Some (indom_app D0) = Some f. rewrite indom_app_eq. simpl. by rewrite E0.
          case: ea => ea. rewrite ea in hv. by apply hv.
          apply negbT. by apply negbF_imp => e0 ; rewrite (eqP e0) in el ; rewrite eq_refl in el.
      - move => X.
        specialize (ufe (updMap l (IVal t' s) (Unfold w))).
        have uf:=proj2 ufe l1. rewrite X in uf. by rewrite E' in uf.
  + rewrite subSS. rewrite subn0. case: k Ig Is hv ; first by []. move => k Ig Is hv.
    have P:l \in dom (Unfold
          (Fold (updMap l (IVal t' s) (Unfold w)))).
      specialize (ufe (updMap l (IVal t' s) (Unfold w))). rewrite (proj1 ufe).
      rewrite findom_indom. by rewrite updMap_simpl.
    exists P. move => w' j v1 Lj.
    case_eq ((Unfold (Fold (updMap l (IVal t' s) (Unfold w)))) l) ; last by
        move => ee; have F:(Some (indom_app P) = None) by rewrite (indom_app_eq P) ; rewrite ee.
    move => f ee.
    have ea:Some (indom_app P) = Some f. rewrite indom_app_eq. by rewrite ee.
    case: ea => ea. rewrite ea. simpl. specialize (ufe (updMap l (IVal t' s) (Unfold w))).
    have uuff:=proj2 ufe l. rewrite ee in uuff. rewrite updMap_simpl in uuff.
    have uff:= uuff w' (j,v1). simpl in uff. apply uff.
- move => v _ IH. move => k s ts g w Ig Is j Lj h h' v' ev hv. inversion ev. clear h0 H2. clear v0 H3. rewrite <- H0 in Lj.
  have A:=(proj2 (cev ev)). rewrite (eq_irrelevance (proj2 (cev ev)) A). rewrite H1 in H4.
  exists w. split ; first by []. rewrite <- H0. clear ev j H0.
  have ee:h = h' by apply heap_eq. rewrite ee in hv. clear h ee H1.
  specialize (IH k).
  split ; first by apply (heap_world_down (leq_subr 1 k) hv).
  specialize (IH s ts g w Ig Is). simpl in IH. case: k IH Ig Is Lj hv ; first by [].
  rewrite <- H. move => k IH Ig Is _ hv. rewrite subSS. rewrite subn0. specialize (hv k (ltnSn _)).
  case: IH => D IH.
  specialize (IH w k (CValue _ A) (ltnSn _)). rewrite <- IH. clear IH.
  have X:=findom_indom (heap h') l. rewrite H4 in X. have B:=proj2 hv. specialize (B l).
  specialize (B D X).
  have ae:CValue _ (heap_cl X) = CValue _ A. apply CValue_eq.
    have ea:Some (indom_app X) = Some v'. by rewrite indom_app_eq. by case: ea => ea.
  rewrite ae in B. by apply B.
- move => v0 v1 t' _ IH0 _ IH1 e. rewrite e. clear e t. move => k s ts g w Ig Is j Lj h h' v ev hv.
  inversion ev. clear v2 H2. clear h0 H1. move: ev. rewrite <- H3. clear v H3.
  rewrite <- H0 in Lj. rewrite <- H0. move => ev. clear j H0.
  exists w. split ; first by [].
  case: k Lj hv Ig Is ; first by []. move => k _ hv Ig Is.
  rewrite subSS. rewrite subn0. split ; last by [].
  specialize (IH0 _ s ts g w Ig Is). simpl in IH0. rewrite <- H in IH0. clear v0 H ev.
  specialize (IH1 _ s ts g w Ig Is).
  split.
  + rewrite <- H5. rewrite dom_updMap ; last by rewrite findom_indom.
    specialize (hv 0 (ltn0Sn _)). by rewrite (proj1 hv).
  + move => l0 I I'. case_eq (l == l0) => A.
    * have e:Some (indom_app I) = Unfold w l. rewrite indom_app_eq. by rewrite (eqP A).
      simpl in IH0. destruct IH0 as [D IH0].
      case_eq (Unfold w l) ; last by rewrite <- e.
      move => f ee. rewrite ee in e. simpl in e. case: e => e.
      rewrite e. specialize (IH0 w).
      have ed:Some (indom_app D) = Some (f). by rewrite indom_app_eq. case: ed => ed. rewrite ed in IH0. simpl in IH0.
      move: I'. clear e I. rewrite <- (eqP A). clear l0 A.
      move => I. have A:=heap_cl I. rewrite (eq_irrelevance (heap_cl I) A).
      have ea:Some (indom_app I) = Some (substV (map (@cval _) (Prod_subst g)) (vtsubst (Prod_subst ts) v1)).
        rewrite indom_app_eq. rewrite <- H5. by rewrite updMap_simpl.
      case: ea => ea. move: A. rewrite ea. clear I ea. move => A.
      specialize (IH0 j (CValue _ A)).
      specialize (IH0(ssrnat.ltn_trans H (ltnSn _))).
      apply (proj2 IH0). apply: (upred_fun_imp _ (upred_downclosed _ IH1)). by apply (leqW (ltnW H)).
    * specialize (hv j (ltnW H)). destruct hv as [D hv].
      have ne:(l != l0) by rewrite A.
      specialize (hv l0 I). have I0:l0 \in dom (heap h). rewrite <- H5 in I'. rewrite dom_updMap in I'. by apply I'. rewrite findom_indom. by apply H4.
      specialize (hv I0). have ee: CValue _ (heap_cl I0) = CValue _ (heap_cl I'). apply CValue_eq.
      have ee:Some (indom_app I0) = Some (indom_app I'). do 2 rewrite indom_app_eq.
      rewrite <- H5. rewrite updMap_simpl2. by [].
        apply negbT. by apply negbF_imp => e0 ; rewrite (eqP e0) in ne ; rewrite eq_refl in ne.
      by case: ee => ee. by rewrite ee in hv.
- move => t' v0 v1 D0 IH0 D1 IH1. move => k s ts g w Ig Is. simpl.
  move => j Lj h h' v ev hv. inversion ev. clear H2 h0 H0 H3 H4 h1 n H v2 v3.
  specialize (IH0 k s ts g w Ig Is). simpl in IH0. rewrite <- H1 in IH0.
  specialize (IH1 k s ts g w Ig Is).
  specialize (IH0 w k _ (Ole_refl _) (leqnn _) IH1).
  specialize (IH0 j Lj h h' _ X hv). destruct IH0 as [w' [Lw [hw IH0]]]. exists w'. split ; first by [].
  split ; first by []. by apply (upred_fun_imp _ IH0).
- move => v0 t0 t1 _ IH e. rewrite e. clear t e. move => k s ts g w Ig Is. specialize (IH k s ts g w Ig Is).
  move => j Lj h h' v ev hv. inversion ev. clear h0 H0 v1 H3 h1 H4 n H t H2.
  have A:=(cvalueP (csubstV (Prod_subst g) (vtsubst (Prod_subst ts) v0))). simpl in IH.
  rewrite (eq_irrelevance (cvalueP (csubstV (Prod_subst g) (vtsubst (Prod_subst ts) v0))) A) in IH.
  move: A IH. simpl. rewrite <- H1. move => A IH.
  specialize (IH (tsubst (Prod_subst ts) t1) (IVal t1 s) w k (leqnn _) (Ole_refl _)).
  specialize (IH j Lj h h' _ X hv).
  case: IH => w'. case => Lw. case => hv' IH. exists w'. split ; first by []. split ; first by [].
  have B:=proj1 (IVal_subst t0 _ w' (k - j, CValue v (proj2 (cev ev)))).
  have C:= B _ _ (t1 :: idsub 0 i) s. clear B.
  apply (C (s, (IVal t1 s))) ; last apply (upred_fun_imp _ IH).
  case ; first by []. move => l P. simpl. rewrite (@nth_idsub i 0 l P). simpl. 
  by rewrite (eq_irrelevance (@ltn_addl l i O P) P).
- move => v e0 e1 t0 t1 _ IHv _ IH0 _ IH1. move => k s ts g w Ig Is.
  move => j Lj h h' vr ev hv. specialize (IHv k s ts g w Ig Is). simpl in IHv.
  specialize (IH0 k s). specialize (IH1 k s).
  have A:=(closedV_sub (vtsubst (Prod_subst ts) v) (map_closed (Prod_subst g))).
  rewrite (eq_irrelevance (closedV_sub (vtsubst (Prod_subst ts) v) (map_closed (Prod_subst g))) A) in IHv.
  inversion ev ; clear h0 H0 h1 H5 n H e2 H2 e3 H3 v1 H4.
  + move: A IHv. rewrite <- H1. move => A IHv. specialize (IH0 ts (g,(CValue v0 A)) w (conj Ig IHv) Is).
    specialize (IH0 j Lj h h'). rewrite substE_map in X. simpl in X. do 2 rewrite map_map in X.
    specialize (IH0 vr). simpl in IH0.
    have e:(map (fun (x:cvalue O) => substV [:: v0] (shiftV 0 1 x)) (Prod_subst g)) = map (@cval _) (Prod_subst g).
      apply: eq_map. move => x. simpl. have AA:= @substV_shiftW 1 0 x 0 [:: v0] [::] (refl_equal _) (refl_equal _).
      rewrite AA. by rewrite substV_cid.
    rewrite e in X. specialize (IH0 X hv).
    destruct IH0 as [w' [Lw [hv' IH0]]]. exists w'. split ; first by []. split ; first by [].
    by apply (upred_fun_imp _ IH0).
  + move: A IHv. rewrite <- H1. move => A IHv. specialize (IH1 ts (g,CValue v0 A) w (conj Ig IHv) Is).
    specialize (IH1 j Lj h h'). rewrite substE_map in X. simpl in X. do 2 rewrite map_map in X. specialize (IH1 vr).
    simpl in IH1.
    have e:(map (fun (x:cvalue O) => substV [:: v0] (shiftV 0 1 x)) (Prod_subst g)) = map (@cval _) (Prod_subst g).
      apply: eq_map. move => x. simpl. have AA:= @substV_shiftW 1 0 x 0 [:: v0] [::] (refl_equal _) (refl_equal _).
      rewrite AA. by rewrite substV_cid.
    rewrite e in X. specialize (IH1 X hv).
    destruct IH1 as [w' [Lw [hv' IH1]]]. exists w'. split ; first by []. split ; first by [].
    by apply (upred_fun_imp _ IH1).
Qed.

