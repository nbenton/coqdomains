Require Import Predom.
Require Import PredomAux.
Require Export lc.
Require Import PredomSum.
Require Export untypedlambda.
Require Import PredomCore.
Require Import PredomLift.
Require Import PredomKleisli.
Require Import PredomProd.

Set Implicit Arguments.
Unset Strict Implicit.


Definition SimpleOp2mm (A B C : Type) (op : A -> B -> C) : Discrete A -> Discrete B -m>  Discrete C.
intros.
exists (op X).
unfold monotonic.
intros.
simpl in *.
rewrite H. auto.
Defined.

Definition SimpleOp2c A B C (op:A -> B -> C) :
    Discrete A -> Discrete B -c> Discrete C.
intros.
exists (SimpleOp2mm op X).
simpl in *.
unfold continuous.
intros.
simpl. auto.
Defined.

Definition SimpleOp2m (A B C:Type) (op : A -> B -> C) :
    Discrete A -m> Discrete B -C-> Discrete C.
intros.
exists (SimpleOp2c op).
unfold monotonic.
intros.
simpl in *.
rewrite H. auto.
Defined.

Definition SimpleOp2 A B C (op:A -> B -> C) :
    Discrete A -c> Discrete B -C-> Discrete C.
intros.
exists (SimpleOp2m op).
unfold continuous ; intros ; simpl ; auto.
Defined.

Definition FS := BiLift_strict (BiSum (BiConst (Discrete nat)) BiArrow).
Definition DInf := DInf FS.
Definition VInf := Dsum (Discrete nat) (DInf -C-> DInf).

Definition Roll : DL VInf -C-> DInf := ROLL FS.
Definition Unroll : DInf -C-> DL VInf := UNROLL FS.

Lemma UR_eq : forall x, Unroll (Roll x) == x.
intros y. rewrite <- fcont_comp_simpl.
apply Oeq_trans with (y:= ID y).
refine (app_eq_compat _ (Oeq_refl _)). unfold Unroll. unfold Roll. apply (DIso_ur FS). auto.
Qed.

Lemma RU_eq : forall x, Roll (Unroll x) == x.
intros x.
assert (xx := fcont_eq_elim (DIso_ru FS) x). rewrite fcont_comp_simpl in xx. rewrite ID_simpl in xx.
simpl in xx. unfold Unroll. unfold Roll. apply xx.
Qed.

Definition monic D E (f:D -c> E) := forall x y, f x <= f y -> x <= y.

Lemma Roll_monic: monic Roll.
unfold monic.
assert (zz:=@ROLL_monic _ FS). fold Roll in zz. fold DInf in zz. unfold VInf.
apply zz.
Qed.

Lemma Unroll_monic: monic Unroll.
assert (yy:=@UNROLL_monic _ FS). fold Unroll in yy. fold DInf in yy.
unfold monic. apply yy.
Qed.

Lemma inj_monic: forall D E  (f:D -c> E), monic f -> forall x y, f x == f y -> x == y.
intros D E f mm. unfold monic in mm. intros x y.
assert (xx:= mm x y). specialize (mm y x).
intros [xy1 xy2]. split ; auto.
Qed.

Fixpoint SemEnv (env : Env) :=
match env with
| O => DOne
| S env' => SemEnv env' *c* VInf
end.

(* Lookup in an environment *)
Fixpoint SemVar env (var : Var env) : SemEnv env -c> VInf :=
  match var with
  | ZVAR _ => SND
  | SVAR _ v => SemVar v << FST
  end.

Lemma K_com2: forall E F (f:E -C-> F),
              EV << PROD_fun (@K E _ f) (ID) == f.
intros. apply fcont_eq_intro. auto.
Qed.

Lemma uncurry_PROD_fun: forall D D' E F G f g1 (g2:G -C-> D') h,
  @uncurry D E F f << PROD_fun (g1 << g2) h == @uncurry D' E F (f << g1) << PROD_fun g2 h.
intros. apply fcont_eq_intro. auto.
Qed.

Add Parametric Morphism D E F : (@curry D E F)
with signature (@Oeq (Dprod D E -C-> F)) ==> (@Oeq (D -C-> E -C-> F))
as Curry_eq_compat.
intros f0 f1 feq. refine (fcont_eq_intro _). intros d. refine (fcont_eq_intro _). intros e.
repeat (rewrite curry_simpl). auto.
Qed.

Definition Dlift : (VInf -C-> DInf) -C-> DInf -C-> DInf := curry (Roll << EV <<
     PROD_map (kleisli_cc _ _ << (fcont_COMP VInf DInf _ Unroll)) Unroll).

Definition Dapp := EV << PROD_map (SUM_fun (PBot : Discrete nat -C-> DInf -C-> DL VInf)
                                               (fcont_COMP _ _ _ Unroll))
                                      (Roll << eta) : Dprod VInf VInf -C-> DL VInf.

Definition zeroCasem : Discrete nat -m> Dsum DOne (Discrete nat).
exists (fun (n:Discrete nat) => match n with | O => INL DOne _ tt | S m => INR _ (Discrete nat) m end).
unfold monotonic. intros x y xy. assert (x = y) as E by auto.
rewrite E in *. auto.
Defined.

Definition zeroCase : Discrete nat -c> Dsum DOne (Discrete nat).
exists zeroCasem. unfold continuous. intros c.
refine (Ole_trans _ (le_lub _ 0)). auto.
Defined.

Lemma zeroCase_simplS: forall n, zeroCase (S n) = INR _ (Discrete nat) n.
intros n ; auto.
Qed.

Lemma zeroCase_simplO: zeroCase O = INL DOne _ tt.
auto.
Qed.

Fixpoint SemVal env (v : Value env) : SemEnv env -C-> VInf :=
match v with
| NUM _ n => INL _ _ << (@K _ (Discrete nat) n)
| VAR _ var => SemVar var
| LAMBDA _ e => INR _ _ << Dlift << curry (Roll << SemExp e)
end
with SemExp env (e : Exp env) : SemEnv env -C-> VInf _BOT :=
match e with
| APP _ v1 v2 => Dapp <<  <| SemVal v1 , SemVal v2 |>
| VAL _ v => eta << (SemVal v)
| LET _ e1 e2 => EV << PROD_fun (curry (KLEISLIR (SemExp e2))) (SemExp e1)
| OP _ op v1 v2 =>
       uncurry _ _ _ (Operator2 (eta << INL _ _ << uncurry _ _ _ (SimpleOp2 op))) <<
       PROD_fun (SUM_fun eta (PBot : (DInf -C-> DInf) -C-> DL (Discrete nat)) << SemVal v1)
                (SUM_fun eta (PBot : (DInf -C-> DInf) -C-> DL (Discrete nat)) << SemVal v2)
| IFZ _ v e1 e2 => EV <<
        PROD_fun (SUM_fun (SUM_fun (K _ (SemExp e1)) (K _ (SemExp e2)) << zeroCase)
                          (PBot : (DInf -C-> DInf) -C-> SemEnv _ -C-> DL VInf ) << (SemVal v)) ID
end.

Lemma EV_simpl: forall D E (f : D -C-> E) d, EV (f,d) = f d.
intros ; auto.
Qed.


Add Parametric Morphism env (e : Exp env) : (SemExp e)
with signature (@Oeq (SemEnv env)) ==> (@Oeq (DL VInf))
as SemExp_eq_compat.
intros e0 e1 eeq.
destruct eeq. split ; auto.
Qed.

Add Parametric Morphism env (v : Value env) : (SemVal v)
with signature (@Oeq (SemEnv env)) ==> (@Oeq VInf)
as SemVal_eq_compat.
intros e0 e1 eeq.
destruct eeq. split ; auto.
Qed.

