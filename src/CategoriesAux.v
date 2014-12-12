Lemma catProdSetoidAxiom (C C' : catType) (x y : C * C') : @Setoid.axiom (C (fst x) (fst y) * C' (snd x) (snd y)) (fun f f' => fst f =-= fst f' /\ snd f =-= snd f').
move => C C'. case => X Y. case => Z W. split ; first by [].
split.
- simpl. case => f g. case => f' g'. case => h h'. simpl.
  move => [P Q]. move => [P' Q']. split ; [by apply (tset_trans P P') | by apply (tset_trans Q Q')].
- simpl. case => f g. case => f' g'. simpl. move => [P Q]. rewrite P. by rewrite Q.
Qed.

Canonical Structure catProdSetoidMixin (C C' : catType) (x y : C * C') := SetoidMixin (catProdSetoidAxiom x y).
Canonical Structure catProdSetoid (C C' : catType) (x y : C * C') := Eval hnf in SetoidType (catProdSetoidMixin x y).

Lemma prodCatAxiom (C C' : catType) : @Category.axiom (C * C') (@catProdSetoid C C') 
  (fun X Y Z f g => (fst f << fst g,snd f << snd g)) (fun X => (Id,Id)).
move => C C'. split ; last split ; last split ; simpl.
- case => X Y. case => Z W. case => f f'. by do 2 rewrite comp_idL.
- case => X Y. case => Z W. case => f f'. by do 2 rewrite comp_idR.
- case => X Y. case => Z W. case => N M. case => A B. simpl. case => f f'.
  case => g g'. case => h h'. simpl. by do 2 rewrite comp_assoc.
- case => X Y. case => Z W. case => N M. simpl. case => f f'. case => g g'. case => h h'. case => k k'.
  simpl. case => e0 e1. case => e2 e3. rewrite -> e0. rewrite -> e1. rewrite -> e2. by rewrite -> e3.
Qed.

Canonical Structure prod_catMixin C C' := CatMixin(prodCatAxiom C C').
Definition prod_catType C C' := Eval hnf in CatType (prod_catMixin C C').

Definition iso (C:catType) X Y (f:C X Y) (f':C Y X) : Prop := f << f' =-= Id /\ f' << f =-= Id.

Module CatMon.

Definition axiom (C:catType) (F:functor (prod_catType C C) C) (I:C)
    (a:forall X Y Z:C, F(F(X,Y),Z) =-> F(X,F(Y,Z)))
    (aI:forall X Y Z:C, F(X,F(Y,Z)) =-> F(F(X,Y),Z))
              (l:forall X, F(I,X) =-> X) (lI:forall X, X =-> F(I,X)) 
              (r:forall X, F(X,I) =-> X) (rI:forall X, X =-> F(X,I)) :=
  forall X Y Z X' Y' Z' (f:C X X') (g:C Y Y') (h:C Z Z'), iso (a X Y Z) (aI X Y Z) /\ iso (l X) (lI X) /\ iso (r X) (rI X) /\
     a _ _ _ << @functor_morph _ _ F (_,Z) (_,Z') (@functor_morph _ _ F (X,Y) (X',Y') (f,g),h) =-=
     @functor_morph _ _ F (X,_) (X',_) (f,@functor_morph _ _ F (Y,Z) (Y',Z') (g,h)) << a _ _ _ /\
       r _ << @functor_morph _ _ F (X,I) (X',I) (f,Id) =-= f << r _ /\
       l _ << @functor_morph _ _ F (I,X) (I,X') (Id,f) =-= f << l _ /\
       forall W, a _ _ _ << a (F (X,Y)) Z W =-= 
         @functor_morph _ _ F (X,F(F(Y,Z),W)) (X,F(Y,F(Z,W))) (Id,a Y Z W) << a _ _ _ <<
         @functor_morph _ _ F (_,W) (_,W) (a X Y Z,Id) /\
       @functor_morph _ _ F (X,F(I,Y)) (X,Y) (Id, l Y) << a X I Y =-= 
       @functor_morph _ _ F (F(X,I),Y) (X,Y) (r X,Id).

Record mixin_of (C:catType) : Type := Mixin
{ 
  tensor:functor (prod_catType C C) C;
  unit : C;
  assoc:forall X Y Z:C, tensor(tensor(X,Y),Z) =-> tensor(X,tensor(Y,Z));
  assocI:forall X Y Z:C, tensor(X,tensor(Y,Z)) =-> tensor(tensor(X,Y),Z);
  lid:forall X, tensor(unit,X) =-> X;
  lidI:forall X, X =-> tensor(unit,X);
  rid:forall X, tensor (X,unit) =-> X;
  ridI:forall X, X =-> tensor (X,unit);
  _ : @axiom C tensor unit assoc assocI lid lidI rid ridI
}.

Record class_of (T:Type) (M:T -> T -> setoidType) : Type :=
  Class { base :> Category.class_of M ; ext :> mixin_of (Category.Pack base T) }.

Structure cat : Type := Pack {object :> Type; morph :> object -> object -> setoidType ; _ : class_of morph; _ : Type}.
Definition class cT := let: Pack _ _ c _ := cT return class_of cT in c.
Definition unpack (K:forall O (M:O -> O -> setoidType) (c:class_of M), Type)
            (k : forall O (M: O -> O -> setoidType) (c : class_of M), K _ _ c) (cT:cat) :=
  let: Pack _ M c _ := cT return @K _ _ (class cT) in k _ _ c.
Definition repack cT : _ -> Type -> cat := let k T M c p := p c in unpack k cT.
Definition pack := let k T M c m := Pack (@Class T M c m) T in Category.unpack k.

Coercion catType (cT:cat) := Category.Pack (class cT) cT.

End CatMon.

Notation monCat := CatMon.cat.
Notation monCatMixin := CatMon.Mixin.
Notation monCatType := CatMon.pack.

Canonical Structure CatMon.catType.

Definition tensor (C:monCat) : functor (prod_catType C C) C := CatMon.tensor (CatMon.class C).
Implicit Arguments tensor [C].

Definition tunit (C:monCat) : C := CatMon.unit (CatMon.class C).
Implicit Arguments tunit [C].

Definition tassoc (C:monCat) (X Y Z:C) : tensor (tensor (X,Y),Z) =-> tensor(X,tensor(Y,Z)) := CatMon.assoc (CatMon.class C) X Y Z.

Definition tassocI (C:monCat) (X Y Z:C) : tensor(X,tensor(Y,Z)) =-> tensor (tensor (X,Y),Z) := CatMon.assocI (CatMon.class C) X Y Z.

Definition tidL (C:monCat) X : tensor(tunit,X) =-> X := CatMon.lid (CatMon.class C) X.
Definition tidR (C:monCat) X : tensor (X,tunit) =-> X := CatMon.rid (CatMon.class C) X.
Definition tidLI (C:monCat) X : X =-> tensor (tunit,X) := CatMon.lidI (CatMon.class C) X.
Definition tidRI (C:monCat) X : X =-> tensor (X,tunit) := CatMon.ridI (CatMon.class C) X.

Lemma tassoc_natural (C:monCat) X Y Z X' Y' Z' (f:C X X') (g:C Y Y') (h:C Z Z') :
     tassoc _ _ _ << @functor_morph _ _ tensor (_,Z) (_,Z') (@functor_morph _ _ tensor (X,Y) (X',Y') (f,g),h) =-=
     @functor_morph _ _ tensor (X,_) (X',_) (f,@functor_morph _ _ tensor (Y,Z) (Y',Z') (g,h)) << tassoc _ _ _.
unfold tassoc. unfold tensor. case => A M. case. move => B. case. simpl.
move => ten I assoc assocI lid lidI rid ridI Ax. move => C X Y Z X' Y' Z' f g h.
apply (proj1 (proj2 (proj2 (proj2 (Ax X Y Z X' Y' Z' f g h))))).
Qed.

Lemma tassoc_iso (C:monCat) X Y Z : iso (@tassoc C X Y Z) (tassocI X Y Z).
unfold tassoc, tassocI.
case => A M. case. move => B. case. simpl.
move => ten I assoc assocI lid lidI rid ridI Ax. move => C X Y Z.
by apply (proj1 (Ax X Y Z X Y Z Id Id Id)).
Qed.

Lemma tassocI_natural (C:monCat) X Y Z X' Y' Z' (f:C X X') (g:C Y Y') (h:C Z Z') :
     @functor_morph _ _ tensor (_,Z) (_,Z') (@functor_morph _ _ tensor (X,Y) (X',Y') (f,g),h) << tassocI _ _ _ =-=
     tassocI _ _ _ << @functor_morph _ _ tensor (X,_) (X',_) (f,@functor_morph _ _ tensor (Y,Z) (Y',Z') (g,h)).
move => C X Y Z X' Y' Z' f g h.
rewrite <- (comp_idL (@functor_morph _ _ tensor (_,Z) (_,Z') (@functor_morph _ _ tensor (X,Y) (X',Y') (f,g),h))).
rewrite <- (proj2 (tassoc_iso X' Y' Z')). rewrite <- (comp_assoc _ (tassoc X' Y' Z') _).
rewrite tassoc_natural. do 2 rewrite <- comp_assoc. rewrite (proj1 (tassoc_iso X Y Z)).
by rewrite comp_idR.
Qed.

Lemma tidR_natural (C:monCat) X X' (f:C X X') : tidR _ << @functor_morph _ _ tensor (X,tunit) (X',tunit) (f,Id) =-= f << tidR _.
unfold tensor, tunit, tidR.
case => A M. case. move => B. case. simpl.
move => ten I assoc assicI lid lidI rid ridI Ax. move => C X X' f.
apply (proj1 (proj2 (proj2 (proj2 (proj2 (Ax X X X X' X' X' f f f)))))).
Qed.

Lemma tidL_natural (C:monCat) X X' (f:C X X') : tidL _ << @functor_morph _ _ tensor (tunit,X) (tunit,X') (Id,f) =-= f << tidL _.
unfold tensor, tunit, tidL.
case => A M. case. move => B. case. simpl.
move => ten I assoc assocI lid lidI rid ridI Ax. move => C X X' f.
apply (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (Ax X X X X' X' X' f f f))))))).
Qed.

Lemma tidL_iso (C:monCat) (X:C) : iso (tidL X) (tidLI _).
unfold tidL, tidLI.
case => A M. case. move => B. case. simpl.
move => ten I assoc assocI lid lidI rid ridI Ax. move => C X.
by apply (proj1 (proj2 (Ax X X X X X X Id Id Id))).
Qed.

Lemma tidR_iso (C:monCat) (X:C) : iso (tidR X) (tidRI _).
unfold tidR, tidRI.
case => A M. case. move => B. case. simpl.
move => ten I assoc assocI lid lidI rid ridI Ax. move => C X.
by apply (proj1 (proj2 (proj2 (Ax X X X X X X Id Id Id)))).
Qed.

Lemma tidLI_natural (C:monCat) X X' (f:C X X') : @functor_morph _ _ tensor (tunit,X) (tunit,X') (Id,f) << tidLI _ =-= tidLI _ << f.
move => C X X' f.
rewrite <- (comp_idL (@functor_morph _ _ tensor (tunit, X) (tunit, X') (Id, f))).
rewrite <- (proj2 (tidL_iso X')). rewrite <- (comp_assoc _ _ (tidLI X')).
rewrite tidL_natural. do 2 rewrite <- comp_assoc. rewrite (proj1 (tidL_iso X)).
by rewrite comp_idR.
Qed.

Lemma tidRI_natural (C:monCat) X X' (f:C X X') : @functor_morph _ _ tensor (X,tunit) (X',tunit) (f,Id) << tidRI _ =-= tidRI _ << f.
move => C X X' f.
rewrite <- (comp_idL (@functor_morph _ _ tensor (X,tunit) (X',tunit) (f, Id))).
rewrite <- (proj2 (tidR_iso X')). rewrite <- (comp_assoc _ _ (tidRI X')).
rewrite tidR_natural. do 2 rewrite <- comp_assoc. rewrite (proj1 (tidR_iso X)).
by rewrite comp_idR.
Qed.

Lemma tassoc_unit_com (C:monCat) X Y :
       @functor_morph _ _ tensor (X,tensor(tunit,Y)) (X,Y) (Id, tidL Y) << tassoc X (@tunit C) Y =-= 
       @functor_morph _ _ tensor (tensor(X,tunit),Y) (X,Y) (tidR X,Id).
unfold tensor, tunit, tidR, tidL, tassoc.
case => A M. case. move => B. case. simpl.
move => ten I assoc assocI lid lidI rid ridI Ax. move => C X Y.
apply (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (Ax X Y X X Y X Id Id Id)))))) X)).
Qed.

Lemma tassoc_com (C:monCat) X Y Z W :  tassoc _ _ _ << tassoc (tensor (X,Y)) Z W =-= 
         @functor_morph _ _ tensor (X,tensor(tensor(Y,Z),W)) (X,tensor(Y,tensor(Z,W))) (Id,tassoc Y Z W) << tassoc _ _ _ <<
         @functor_morph _ C tensor (_,W) (_,W) (tassoc X Y Z,Id).
unfold tensor, tunit, tidR, tidL, tassoc.
case => A M. case. move => B. case. simpl.
move => ten I assoc assocI lid lidI rid ridI Ax. move => C X Y Z W.
apply (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (Ax X Y Z X Y Z Id Id Id)))))) W)).
Qed.

Lemma ProdF_id (C:prodCat) : forall X : prod_catType C C, (|fst (@Category.id _ X), snd (@Category.id _ X)|) =-= Id.
move => C X. simpl.
by apply: prod_unique ; [rewrite prod_fun_fst | rewrite prod_fun_snd] ; rewrite comp_idL ; rewrite comp_idR.
Qed.

Lemma ProdF_comp (C:prodCat) : forall (X Y Z : prod_catType C C)
     (f : prod_catType C C Y Z)
     (g : prod_catType C C X Y),
   (|fst (f << g), snd (f << g)|) =-= (|fst f, snd f|) << (|fst g, snd g|).
move => C X Y Z f g. simpl. rewrite prod_map_prod_fun. by do 2 rewrite comp_assoc.
Qed.

Definition prod_functor (C:prodCat) : functor (prod_catType C C) C :=
  @mk_functor (prod_catType C C) C
     (fun p => fst p * snd p) (fun X Y f => (|fst f,snd f|)) (@ProdF_id C) (@ProdF_comp C).

Module CatProdTerminal.

Record class_of (T:Type) (M:T -> T -> setoidType) : Type :=
  Class { base :> CatProduct.class_of M ; terminal :> CatTerminal.mixin_of (Category.Pack base T) }.

Coercion base2 T (M:T -> T -> setoidType) (c:class_of M) := CatTerminal.Class c.

Structure cat : Type := Pack {object :> Type; morph :> object -> object -> setoidType ; _ : class_of morph; _ : Type}.
Definition class cT := let: Pack _ _ c _ := cT return class_of cT in c.
Definition unpack (K:forall O (M:O -> O -> setoidType) (c:class_of M), Type)
            (k : forall O (M: O -> O -> setoidType) (c : class_of M), K _ _ c) (cT:cat) :=
  let: Pack _ M c _ := cT return @K _ _ (class cT) in k _ _ c.
Definition repack cT : _ -> Type -> cat := let k T M c p := p c in unpack k cT.
Definition pack := let k T M c m := Pack (@Class T M c m) T in CatProduct.unpack k.

Coercion prodCat cT := CatProduct.Pack (class cT) cT.
Definition catType cT := Category.Pack (class cT) cT.
Coercion terminalCat cT := CatTerminal.Pack (class cT) cT.

End CatProdTerminal.

Notation prodTerminalCat := CatProdTerminal.cat.
Notation prodTerminalCatType := CatProdTerminal.pack.
Canonical Structure CatProdTerminal.catType.
Canonical Structure CatProdTerminal.prodCat.
Canonical Structure CatProdTerminal.terminalCat.

Canonical Structure cpoProdTerminalType := Eval hnf in prodTerminalCatType cpoTerminalMixin.
Canonical Structure ordPordTerminalType := Eval hnf in prodTerminalCatType ordTerminalMixin.

Lemma prod_fun_unique (C:prodCat) (X Y Z:C) (f f':X =-> Y) (g g':X =-> Z) :
   f =-= f' -> g =-= g' -> <| f, g|> =-= <|f',g'|>.
move => C X Y Z f f' g g' e e'.
apply prod_unique ; by [do 2 rewrite prod_fun_fst | do 2 rewrite prod_fun_snd].
Qed.

Lemma prod_eta (C:prodCat) (X Y:C) : <| pi1, pi2 |> =-= (@Category.id C (X * Y)).
move => C X Y. apply prod_unique ; rewrite comp_idR.
by rewrite prod_fun_fst.
by rewrite prod_fun_snd.
Qed.

Lemma prodMonAxiom (C:prodTerminalCat) :
  @CatMon.axiom C (@prod_functor C) One (fun X Y Z => <|pi1 << pi1,<|pi2 << pi1,pi2|>|>) 
                  (fun X Y Z => <| <| pi1,pi1 << pi2|>, pi2 << pi2|>)
                      (fun X => pi2) (fun X => <| terminal_morph X, Id|>)
                      (fun X => pi1) (fun X => <| Id, terminal_morph X|>).
move => C X Y Z X' Y' Z' f g h. split ; last split ; last split ; last split ; last split ; last split.
- split.
  + do 2 rewrite prod_fun_prod_fun. rewrite prod_fun_snd. do 2 rewrite <- comp_assoc. do 2 rewrite prod_fun_fst.
    rewrite prod_fun_snd.
    rewrite <- (prod_eta X (Y * Z)). apply: prod_fun_unique ; first by [].
    by apply: prod_unique ; [rewrite prod_fun_fst | rewrite prod_fun_snd].
  + do 2 rewrite prod_fun_prod_fun. rewrite prod_fun_fst. do 2 rewrite <- comp_assoc. do 2 rewrite prod_fun_snd.
    rewrite prod_fun_fst.
    rewrite <- (prod_eta (X * Y) Z). apply: prod_fun_unique ; last by [].
    by apply: prod_unique ; [rewrite prod_fun_fst | rewrite prod_fun_snd].
- split ; first by rewrite prod_fun_snd. apply: prod_unique ; rewrite comp_assoc.
  + rewrite prod_fun_fst. by apply: terminal_unique.
  + rewrite prod_fun_snd. rewrite comp_idL. by rewrite comp_idR.
- split ; first by rewrite prod_fun_fst. apply: prod_unique ; rewrite comp_assoc.
  + rewrite prod_fun_fst. rewrite comp_idL. by rewrite comp_idR.
  + rewrite prod_fun_snd. by apply: terminal_unique.
- simpl. do 3 rewrite prod_fun_prod_fun. apply: prod_fun_unique.
  + do 2 rewrite <- comp_assoc. do 2 rewrite prod_fun_fst. do 2 rewrite comp_assoc. by rewrite prod_fun_fst.
  + do 2 rewrite <- comp_assoc. rewrite -> prod_fun_fst. do 2 rewrite -> prod_fun_snd.
    rewrite prod_map_prod_fun. do 2 rewrite comp_assoc. by rewrite prod_fun_snd.
- simpl. by rewrite prod_fun_fst.
- simpl. by rewrite prod_fun_snd.
- move => W. simpl.
  repeat do ? rewrite prod_map_prod_fun ; do ? rewrite prod_fun_prod_fun.
  split  ; apply: prod_fun_unique ; do ? rewrite comp_idL.
  + do 2 rewrite <- comp_assoc. do 2 rewrite prod_fun_fst. do 2 rewrite comp_assoc. by rewrite prod_fun_fst.
  + apply prod_fun_unique.
    * do 3 rewrite <- comp_assoc. rewrite prod_fun_fst.
      rewrite prod_fun_prod_fun. rewrite prod_fun_fst. rewrite <- comp_assoc. rewrite prod_fun_fst.
      do 2 rewrite (comp_assoc pi1 _ pi2). rewrite prod_fun_snd. rewrite comp_assoc. by rewrite prod_fun_fst.
    * do 3 rewrite <- comp_assoc. rewrite prod_fun_snd.
      rewrite prod_fun_prod_fun. rewrite prod_fun_fst. rewrite <- comp_assoc. rewrite prod_fun_fst.
      do 2 rewrite (comp_assoc pi1 _ pi2). by do 4 rewrite prod_fun_snd.
  + by [].
  + by rewrite prod_fun_snd.
Qed.

Check fun C => monCatMixin (@prodMonAxiom C).
Definition prodTerminalMonMixin C :=  monCatMixin (@prodMonAxiom C).
Definition prodTerminalMonCat C := monCatType (prodTerminalMonMixin C).

Canonical Structure cppoProdTerminalType := Eval hnf in prodTerminalCatType cppoTerminalMixin.

Canonical Structure cppoMon := Eval hnf in monCatType (prodTerminalMonMixin cppoProdTerminalType).

Check fun (X Y : cppoProdCatType) => tensor (X, Y).

(*
Inductive sigP (A:Prop) (P:A -> Prop) : Prop :=
  existP : forall p:A, P p -> sigP P. Check eq_rect.

Lemma catCatSetoidAxiom (C C' : catType) : @Setoid.axiom (functor C C')
   (fun (f f':functor C C') => @sigP (forall (X:C), f X = f' X)
      (fun Q => forall X Y (h:C X Y), functor_morph f h =-= eq_rect (functor_morph f' h) _ (Q X))).
*)



(*
Lemma catProdSetoidAxiom (C C' : catType) : @Setoid.axiom (M C * C') (fun x y 


Lemma prodCatAxiom (C C' : catType) : *)

Open Scope D_scope.


(*
Lemma ordSetoidAxiom D : Setoid.axiom (@Oeq D).
move => D. split ; first by [].
split ; last by apply: Oeq_sym.
by apply: Oeq_trans.
Qed.

Canonical Structure ordSetoidMixin D := SetoidMixin (ordSetoidAxiom D).
Canonical Structure ordSetoidType D := Eval hnf in SetoidType (ordSetoidMixin D).

Canonical Structure cpoSetoidMixin (D:cpoType) := SetoidMixin (ordSetoidAxiom D).
Canonical Structure cpoSetoidType D := Eval hnf in SetoidType (cpoSetoidMixin D).

Coercion ordSetoidType : ordType >-> setoidType.
Coercion cpoSetoidType : cpoType >-> setoidType.
*)

Module Enriched.

Section Enriched.

Variable  M:monCat.

Definition axiom (C:catType) (hom : C -> C -> M) (id : forall (X:C), tunit =-> hom X X)
          (comp : forall (X Y Z : C), tensor (hom Y Z, hom X Y) =-> hom X Z) :=
    forall X Y Z W, comp _ _ _ << @functor_morph _ M tensor (_,tensor _) (hom Z W,hom X Z) (Id,comp X Y Z) <<
                     tassoc (hom Z W) (hom Y Z) (hom X Y) =-=
                   comp _ _ _ << @functor_morph _ M tensor (tensor _,_) (hom Y W,hom X Y) (comp Y Z W,Id) /\
           tidL (hom Y X) =-=  comp _ _ _ << @functor_morph _ M tensor (_,_) (_,_) (id X,Id) /\
           tidR (hom X Y) =-=  comp _ _ _ << @functor_morph _ M tensor (_,tunit) (_,hom X X) (Id,id X).


Record mixin_of (C:catType) := Mixin
  {
    hom : C -> C -> M;
    id : forall (X:C), tunit =-> hom X X;
    comp : forall (X Y Z : C), tensor (hom Y Z, hom X Y) =-> hom X Z;
    _ : axiom id comp
  }.

Record class_of (T:Type) (M:T -> T -> setoidType) : Type := 
  Class { base :> Category.class_of M;
          ext:> mixin_of (Category.Pack base T) }.

Structure cat : Type := Pack {object :> Type; morph :> object -> object -> setoidType ; _ : class_of morph; _ : Type}.
Definition class cT := let: Pack _ _ c _ := cT return class_of (@morph cT) in c.
Definition unpack (K:forall O (M:O -> O -> setoidType) (c:class_of M), Type)
            (k : forall O (M: O -> O -> setoidType) (c : class_of M), K _ _ c) (cT:cat) :=
  let: Pack _ M c _ := cT return @K _ _ (class cT) in k _ _ c.
Definition repack cT : _ -> Type -> cat := let k T M c p := p c in unpack k cT.
Definition pack := let k T M c m := Pack (@Class T M c m) T in Category.unpack k.

Coercion catType (cT:cat) := Category.Pack (class cT) cT.

End Enriched.
End Enriched.

Canonical Structure Enriched.catType.
Notation enrichType := Enriched.cat.
Notation EnrichMixin := Enriched.Mixin.
Notation EnrichType := Enriched.pack.

