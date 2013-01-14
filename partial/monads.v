(****************************************************************)
(*  On monadic parametricity of second-order functionals        *)
(*  by Bauer A., Hofmann M., Karbyshev A.                       *)
(*                                                              *)
(*  Aleksandr Karbyshev                                         *)
(*  May 2012                                                    *)
(*  Build with Coq 8.4 + Ssreflect 1.4                          *)
(****************************************************************)

Set Automatic Coercions Import.
Require Export PredomAll.
Require Import stuff.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Monad.
Section axioms.
Variable T : cpoType -> cpoType.
Variable val : forall X, X =-> T X.
Variable bind : forall X Y, T X =-> (X -=> T Y) -=> T Y.
Definition axiom0 := forall A B f a, @bind A B (@val A a) f =-= f a.
Definition axiom1 := forall A t, @bind A A t (@val A) =-= t.
Definition axiom2 := forall A B C t f g, @bind B C (@bind A B t f) g =-= bind _ _ t (Fcont_app (CCOMP _ _ _ (@bind _ _, f)) g).
End axioms.

Definition axiom T val bind := @axiom0 T val bind /\ @axiom1 T val bind /\ @axiom2 T bind.

Record strictMonad := mkStrictMonad {
  T :> cpoType -> cppoType;
  tval : forall X, X =-> T X;
  tbind : forall X Y, (T X : cpoType) =-> (X -=> T Y) -=> T Y;
  taxiom0 : @axiom0 T tval tbind;
  taxiom1 : @axiom1 T tval tbind;
  taxiom2 : @axiom2 T tbind;
  taxiom3 : forall A B f, @tbind A B PBot f =-= PBot
}.
End Monad.

Notation monadType := Monad.strictMonad.
Notation tval := Monad.tval.
Notation tbind := Monad.tbind.
Notation taxiom0 := Monad.taxiom0.
Notation taxiom1 := Monad.taxiom1.
Notation taxiom2 := Monad.taxiom2.
Notation taxiom3 := Monad.taxiom3.

Definition State (S : cpoType) : monadType.
exists
  (*(fun X => S -=> (X * S) _BOT)*)
  (fun X => exp_cppoType S (liftCppoType (X * S)))
  ((*locked*) (fun X => ((*CURRY*) exp_fun (eta << Id))))
  ((*locked*) (fun X Y =>
     (exp_fun (CCOMP _ _ _ << <| KLEISLI << UNCURRY1 _ _ _ << SND _ _, FST _ _ |>)))).
- rewrite /Monad.axiom0 /=. move => A B f a. apply: fmon_eq_intro => s /=.
  by rewrite kleisliVal.
- rewrite /Monad.axiom1 /=. move => A t. apply: fmon_eq_intro => s /=.
  rewrite UC_id /=.
  have H : eta << Id =-= eta
    by move => X; apply: fmon_eq_intro => x.
  by rewrite H; rewrite kleisli_unit.
- rewrite /Monad.axiom2 /=. move => A B C t f g. apply: fmon_eq_intro => s /=.
  split.
  + apply: DLless_cond => x Hx.
    elim: (kleisliValVal Hx) => vx Hvx. elim: (kleisliValVal (proj1 Hvx)) => vy Hvy.
    rewrite (proj1 Hvy). by rewrite !kleisliVal.
  + apply: DLless_cond => x Hx.
    elim: (kleisliValVal Hx) => vx Hvx.
    rewrite (proj1 Hvx). by rewrite !kleisliVal.
- move => A B f /=. apply: fmon_eq_intro => s /=. by apply: kleisli_bot.
(*- intuition; simpl. apply: fmon_eq_intro => h; simpl.
  split.
  + apply: DLless_cond => x Hx. elim (kleisliValVal Hx) => vx Hvx. simpl in Hvx.
    elim: Hvx => _ Hvx. by elim (PBot_incon_eq (Oeq_sym Hvx)).
  + apply: DLless_cond => x Hx. by elim (PBot_incon_eq (Oeq_sym Hx)).*)
Defined.

Definition valState S := @tval (State S).
Definition bindState S := @tbind (State S).

Lemma valState_simpl S X x s : @tval (State S) X x s =-= Val (x, s).
Proof.
by [].
Qed.

Lemma bindState_simpl S X Y t (f : X =-> (State S Y : cpoType)) s :
  @tbind (State S) X Y t f s =-= kleisli (uncurry f) (t s).
Proof.
by [].
Qed.

Lemma bindState_bot S X Y (t : State S X) :
  bindState S X Y t (@Pointed.least (CPPO.pointedType (exp_cppoType X (State S Y)))) =-= PBot.
Proof.
rewrite /bindState /=. (*unlock; simpl.*)
apply: fmon_eq_intro => h /=. rewrite /bindState /=. unlock; simpl. split.
- apply: DLless_cond => x Hx. elim: (kleisliValVal Hx) => vx Hvx. rewrite /= in Hvx.
  elim: Hvx => _ Hvx. by elim: (PBot_incon_eq (Oeq_sym Hvx)).
- apply: DLless_cond => x Hx. by elim: (PBot_incon_eq (Oeq_sym Hx)).
Qed.

Definition Cont (R : cppoType) : monadType.
exists
  (fun (X : cpoType) => exp_cppoType (X -=> R) R)
  (fun X => (*locked*) (exp_fun (EV _ _ << SWAP)))
  (fun X Y =>
    (*locked*) (exp_fun (exp_fun (EV _ _ << <| FST _ _ << FST _ _, FCONT_app _ _ _ << <| SND _ _, SND _ _ << FST _ _ |> |>)))).
- rewrite /Monad.axiom0 /=. move => A B f a. unlock; simpl. by apply: fmon_eq_intro => h.
- rewrite /Monad.axiom1 /=. move => A t. unlock; simpl. apply: fmon_eq_intro => h /=.
  apply: fmon_eq_compat; by apply: fmon_eq_intro.
- rewrite /Monad.axiom2 /=. move => A B C t f g. unlock; simpl.
  apply: fmon_eq_intro => h /=.
  apply: fmon_eq_compat; by apply: fmon_eq_intro.
- move => A B f /=. unlock; simpl. by apply: fmon_eq_intro => h.
Defined.

Definition valCont R := @tval (Cont R).
Definition bindCont R := @tbind (Cont R).

Lemma valCont_simpl R X x h : @tval (Cont R) X x h =-= h x.
Proof.
by [].
Qed.

Lemma bindCont_simpl R X Y t f h :
  @tbind (Cont R) X Y t f h =-= t (Fcont_app f h).
Proof.
rewrite /=.
apply: (fcont_eq_compat (Oeq_refl _)).
by apply: fcont_eq_intro => x.
Qed.

Definition Lift : monadType.
exists (fun X => liftCppoType X)
       (fun X => @eta X)
       (fun X Y => exp_fun (uncurry (@KLEISLI X Y) << SWAP)).
- rewrite /Monad.axiom0 /= => X Y f x.
  by rewrite kleisliVal.
- rewrite /Monad.axiom1 /= => X t.
  by rewrite kleisli_unit.
- rewrite /Monad.axiom2 /= => X Y Z t f g.
  split.
  + apply: kleisli_leq => y Hy /=.
    elim: (kleisliValVal Hy) => x [Ex Ey].
    exists x. by rewrite Ey kleisliVal.
  + apply: DLless_cond => z Hz.
    elim: (kleisliValVal Hz) => /= x [Ht H].
    by rewrite Ht !kleisliVal /=.
- move => X Y f /=. by rewrite kleisli_bot.
Defined.
