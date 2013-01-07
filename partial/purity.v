(****************************************************************)
(*  On monadic parametricity of second-order functionals        *)
(*  by Bauer A., Hofmann M., Karbyshev A.                       *)
(*                                                              *)
(*  Aleksandr Karbyshev                                         *)
(*  May 2012                                                    *)
(*  Build with Coq 8.4 + Ssreflect 1.4                          *)
(****************************************************************)

Set Automatic Coercions Import.
Require Import PredomLiftClassical.
Require Import relations.
Require Import strategy.
Require Import stuff.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(*Set Printing Width 65.*)

Section Functional.
Variables A B C : cpoType.
Definition FuncType : Type :=
  forall (T : monadType), (A -=> T B) =-> (T C : cpoType).
End Functional.

Section Purity.
Variables A B C : cpoType.

Definition isPure (F : FuncType A B C) : Prop
  := forall (T T' : monadType) (TRacc : TRelAccType T T'),
    ((IdR (X := A) =R=> TRel TRacc (IdR (X := B))) =R=>
       TRel TRacc (IdR (X := C))) (F T) (F T').
End Purity.

Module Domains : DomainParamsType.
  Parameters DA DB DC : cpoType.
End Domains.

Module Import StrategyTree := StrategyTree (Domains).

Definition STree : cppoType := liftCppoType DInf.
Definition Fold := eta << Roll.
Definition Unfold := eta << Unroll.

Definition Ans := Fold << INL _ _.
Definition Que := exp_fun (Fold << INR _ _).

Definition fun2tree (F : FuncType DA DB DC) := F (Cont STree) Que Ans.

Definition Op1 (A B C : cpoType) (f : A =-> B -=> C) (g : A =-> B) : A =-> C := uncurry f << <| Id, g |> .

Lemma Op1_simpl A B C f g a : @Op1 A B C f g a =-= f a (g a).
Proof.
by [].
Qed.

Definition phi (T : monadType) : (DC + DA * (DB -=> DInf _BOT)) =-> (DInf _BOT -=> ((DA -=> T DB) -=> T DC)) -=> ((DA -=> T DB) -=> T DC)
  := [| exp_fun (
          uncurry (@const _ _ (exp_fun (@tval T _ << FST _ _)))
          << SWAP),
        exp_fun (exp_fun (
          Op1
            (@tbind T _ _ <<
              Op1 (SND _ _) (FST _ _ << FST _ _ << FST _ _))
            (exp_fun (
              (Op1
                (uncurry (SND _ _ << FST _ _))
                (uncurry (@const _ _ (SND _ _)) << SWAP)) <<
              <| FST _ _, uncurry (SND _ _ << FST _ _ << FST _ _) |>)
            )))
      |].

Definition phi_inl_simpl (T : monadType) c f h :
  phi T (inl _ c) f h =-= tval T _ c.
by rewrite SUM_fun_simpl.
Qed.

Definition phi_inr_simpl (T : monadType) a k f h :
  phi T (inr _ (a, k)) f h =-= @tbind T _ _ (h a) (Fcont_app ((f : fcont _ _) << k) h).
rewrite /=. rewrite /phi /=.
rewrite SUM_fun_simpl /=.
apply: fmon_eq_compat; first by reflexivity.
by apply: fmon_eq_intro.
Qed.

Definition G (T : monadType) : (DInf _BOT -=> ((DA -=> T DB) -=> T DC)) =->  DInf _BOT -=> ((DA -=> T DB) -=> T DC)
  := CURRY (uncurry (mu1 (phi T << Unroll)) << SWAP).

Lemma G_PBot_simpl (T : monadType) f h : @G T f PBot h =-= PBot.
Proof.
rewrite /=. by rewrite mu1axiom1.
Qed.

Lemma G_Val_simpl (T : monadType) f h d : @G T f (Val d) h =-= phi T (Unroll d) f h.
Proof.
rewrite /=. by rewrite mu1axiom2.
Qed.

Definition tree2funT (T : monadType)
  : exp_cppoType (DInf _BOT) (exp_cppoType (DA -=> T DB) (T DC))
  := fixp (G T).

Lemma tree2funT_eq (T : monadType) :
  tree2funT T =-= G T (@tree2funT T).
Proof.
by apply: fixp_eq.
Qed.

Lemma tree2funT_PBot_simpl (T : monadType) :
  tree2funT T PBot =-= PBot.
Proof.
rewrite /tree2funT fixp_eq. apply: fcont_eq_intro => h.
change (G T (fixp (G T)) PBot h =-= PBot).
by apply: G_PBot_simpl.
Qed.

Lemma tree2funT_Ans_simpl (T : monadType) c h :
  tree2funT T (Ans c) h =-= tval T _ c.
Proof.
rewrite tree2funT_eq /Ans.
rewrite G_Val_simpl.
change (phi T ((Unroll << Roll) (inl _ c)) (tree2funT T) h =-= tval T DC c).
rewrite UR_id. by apply: phi_inl_simpl.
Qed.

Lemma tree2funT_Que_simpl (T : monadType) a k h :
  tree2funT T (Que a k) h =-= tbind T _ _ (h a) (Fcont_app ((tree2funT T : fcont _ _) << k) h).
Proof.
have H := fcont_eq_compat
  (fcont_eq_compat (tree2funT_eq T) (Oeq_refl (Que a k)))
  (Oeq_refl h).
apply (Oeq_trans H).
rewrite G_Val_simpl.
change (phi T ((Unroll << Roll) (inr _ (a, k))) (tree2funT T) h =-= tbind T _ _ (h a) (Fcont_app ((tree2funT T : fcont _ _) << k) h)).
rewrite UR_id. by apply: phi_inr_simpl.
Qed.

Definition treeQuePBot (a : DA) : STree := eta (Roll (inr _ (a, const _ PBot))).

Lemma tree2funT_State_treeQuePBot S a :
  tree2funT (State S) (treeQuePBot a) =-= PBot.
Proof.
rewrite tree2funT_eq /=.
rewrite mu1axiom2.
apply: fmon_eq_intro => h /=.
change ((phi (State S) << (Unroll << Roll)) (inr DC (a, const DB PBot)) (tree2funT _) h =-= PBot).
rewrite UR_id comp_idR.
rewrite phi_inr_simpl.
apply: (Oeq_trans _ (@bindState_bot S _ _ (h a))).
rewrite /bindState. apply: fcont_eq_compat; first by apply: Oeq_refl.
apply: fmon_eq_intro => b.
change (tree2funT (State S) PBot h =-= PBot).
by rewrite tree2funT_PBot_simpl.
Qed.

Definition tree2fun (t : STree) : FuncType DA DB DC.
move => T. by apply: (tree2funT T t).
Defined.

Lemma tree2fun_simpl (t : STree) (T : monadType) :
  @tree2fun t T = tree2funT _ t.
Proof.
by rewrite /tree2fun.
Qed.

(* TODO: move to PredomCore.v *)
Lemma Fcont_app_simpl X Y Z (f : X =-> Y -=> Z) x y : Fcont_app f y x = f x y.
Proof.
by [].
Qed.

Lemma tree2fun_pure (t : STree) : isPure (@tree2fun t).
Proof.
rewrite /isPure. move => T T' TR.
rewrite !tree2fun_simpl.
pose Q : Rel ((STree : cpoType) =-> (DA -=> T DB) -=> T DC) ((STree : cpoType) =-> (DA -=> T' DB) -=> T' DC)
  := fun f f' (*: STree =-> (DA -=> T DB)-=> T DC)*) =>
    forall t, ((@IdR _ =R=>  (TRel TR) DB DB (@IdR _)) =R=>  (TRel TR) DC DC (@IdR _)) (f t) (f' t).
have admQ : admissibleR Q.
  move => c c' H. rewrite /Q => t0.
  apply: admissibleArrR => /=.
  - apply (@Adm _ _ TR). by apply (admissibleIdR).
  - by move => n; apply: H.
suff : Q (tree2funT T) (tree2funT T'); first by [].
apply: {t} fixpR_ind; first by [].
- move => t /=. move => h h' _ /=. by apply: (Str TR).
- move => f f' Hff'. move => t.
  case: (axiom_liftCpo_dec t).
  + move => Heq.
    have Heq1 := (@fcont_eq_compat _ _ (G T f) (G T f) (Oeq_refl _) _ _ (Oeq_sym Heq)).
    have Heq1' := (@fcont_eq_compat _ _ (G T' f') (G T' f') (Oeq_refl _) _ _ (Oeq_sym Heq)).
    apply (axiom_Rel_compat Heq1 Heq1') => {Heq1 Heq1'}.
    move => h h' Hhh'.
    apply: (axiom_Rel_compat (Oeq_sym (@G_PBot_simpl _ f h)) (Oeq_sym (@G_PBot_simpl _ f' h'))).
    by apply: (Str TR).
  + elim => d Hd.
    have Heq1 := (@fcont_eq_compat _ _ (G T f) (G T f) (Oeq_refl _) _ _ (Oeq_sym Hd)).
    have Heq1' := (@fcont_eq_compat _ _ (G T' f') (G T' f') (Oeq_refl _) _ _ (Oeq_sym Hd)).
    apply (axiom_Rel_compat Heq1 Heq1') => {Heq1 Heq1'}.
    move => h h' Hhh'.
    apply: (axiom_Rel_compat (Oeq_sym (@G_Val_simpl _ f h d)) (Oeq_sym (@G_Val_simpl _ f' h' d))).
    elim: (Unroll d) => x.
    * apply: (axiom_Rel_compat (Oeq_sym (@phi_inl_simpl _ _ f h)) (Oeq_sym (@phi_inl_simpl _ _ f' h'))).
      elim: (Acc TR) => [Hval _]. by intuition.
    * elim: x => a k.
      apply: (axiom_Rel_compat (Oeq_sym (@phi_inr_simpl _ a k f h)) (Oeq_sym (@phi_inr_simpl _ a k f' h'))).
      apply: (proj2 (Acc TR)); first by apply Hhh'.
      move => b b' Hbb' /=.
      have Htmp : f' (k b) h' =-= f' (k b') h'.
        apply: fcont_eq_compat; last by [].
        apply: fmon_eq_compat; first by apply Oeq_refl.
        by apply: fmon_eq_compat; first by apply Oeq_refl.
      apply (axiom_Rel_compat (Oeq_refl _) Htmp) => {Htmp}.
      by apply: Hff'.
Qed.

Lemma kleisli_bot_simpl D1 D2 :
  kleisli (PBot : exp_cppoType D1 (liftCppoType D2)) =-=
  (PBot : exp_cppoType (D1 _BOT) (liftCppoType D2)).
Proof.
apply: fcont_eq_intro => x /=.
split => /=; last by apply: leastP.
apply: DLless_cond => d2 H.
elim: (kleisliValVal H ) => {H} /= d1 [_ Hfalse].
by elim: (PBot_incon_eq (Oeq_sym Hfalse)).
Qed.

Theorem tree2fun2tree : forall t, fun2tree (tree2fun t) =-= t.
Proof.
move => t. rewrite /fun2tree tree2fun_simpl.
suff : Fcont_app (Fcont_app (tree2funT (Cont STree)) Que) Ans =-= Id.
  move => H. have H1 := (fcont_eq_compat H (Oeq_refl t)) => {H}.
  by rewrite !Fcont_app_simpl in H1.
clear t.
rewrite -kleisli_unit id_min FIXP_simpl.
rewrite /tree2funT.
pose T := Cont STree.
pose Q : Rel
  (DInf _BOT -=> ((DA -=> T DB) -=> T DC))
  (DInf -=> DInf _BOT)
  := fun f f' => Fcont_app (Fcont_app f Que) Ans =-= kleisli f'.
have admQ : admissibleR Q.
  move => c c' H. rewrite /Q.
  change (Fcont_app (Fcont_app (lub c) Que) Ans =-= KLEISLI (lub c')).
  rewrite lub_comp_eq. apply: fcont_eq_intro => x /=.
  apply: lub_eq_compat. apply: fmon_eq_intro => n /=.
  rewrite /Q in H. by rewrite -(H n).
suff : Q (fixp (G T)) (fixp delta); first by [].
apply: fixpR_ind; first by [].
- rewrite /Q. apply: fcont_eq_intro => x /=.
  apply: Oeq_sym. by rewrite kleisli_bot_simpl.
- move => f f' Hff'.
  rewrite /Q. setoid_rewrite delta_simpl. rewrite /=.
  apply: fcont_eq_intro => t /=.
  case: (axiom_liftCpo_dec t). (* non-constructive step! *)
  + move => Heq. rewrite Heq => {Heq t}.
    rewrite mu1axiom1. by rewrite kleisli_bot.
  + elim => d Hd. rewrite Hd => {Hd t}.
    rewrite mu1axiom2 kleisliVal /=.
    case: (Unroll d) => [c | [a k]] /=.
    * by rewrite !SUM_fun_simpl /= kleisliVal.
    * rewrite (fcont_eq_compat (phi_inr_simpl a k f Que) (Oeq_refl Ans)).
      rewrite SUM_fun_simplx. rewrite bindCont_simpl /=.
      rewrite !kleisliVal /=. apply: Val_eq_compat.
      apply: fcont_eq_compat; first by apply: Oeq_refl.
      change
        (INR DC _ (a, Fcont_app (Fcont_app ((f : fcont _ _) << k) Que) Ans) =-=
         INR DC _ (a, kleisli f' << k)).
      apply: fcont_eq_compat => //.
      apply: pair_cpo_eq_compat => //.
      rewrite /Q in Hff'. rewrite -Hff'.
      by apply: fcont_eq_intro => n.
Qed.

Section conversion.
Variable DS : cppoType.
Variable q : DA =-> (DB -=> DS) -=> (DS (*: cpoType*)).
Variable a : DC =-> (DS : cpoType).

Definition conv := Fcont_app (Fcont_app (@tree2funT (Cont DS)) q) a.

Lemma conv_PBot_simpl : conv PBot =-= PBot.
Proof.
rewrite /conv.
change (tree2funT (Cont DS) PBot q a =-= PBot).
by rewrite tree2funT_PBot_simpl.
Qed.

Lemma conv_Ans_simpl c : conv (Ans c) =-= a c.
Proof.
rewrite /conv.
change (tree2funT (Cont DS) (Ans c) q a =-= a c).
by rewrite tree2funT_Ans_simpl.
Qed.

Lemma conv_Que_simpl a1 h h' : ((@IdR _) =R=>  Gr (conv)) h h' -> conv (Que a1 h) =-= q a1 h'.
Proof.
move => Hhh'.
rewrite /conv.
change (tree2funT (Cont DS) (Que a1 h) q a =-= q a1 h').
rewrite tree2funT_Que_simpl.
rewrite bindCont_simpl.
apply: (fcont_eq_compat (Oeq_refl _)).
apply: fcont_eq_intro => b.
have H := Hhh' b b (IdR_refl _) => {Hhh'}.
rewrite /Gr /conv in H.
rewrite -H /=. by apply: Oeq_refl.
Qed.

Definition TRacc1 : TRelAccType (Cont STree) (Cont DS).
exists
  (fun (X X' : cpoType) (R : Rel X X') => fun (H : Cont STree X) (H' : Cont DS X') =>
    forall h h', (R =R=> Gr conv) h h' -> Gr conv (H h) (H' h')).
- split.
  + intros; simpl; intuition.
  + move => X X' Y Y' Q R f f' t t' H H0.
    move => h h' Hhh'. apply: H => x x' Hxx' /=.
    by eapply H0; eauto.
- move => X X' R Hadm. move => c c' /= H.
  move => h h' Hhh'. rewrite /Gr.
  rewrite lub_comp_eq. apply: lub_eq_compat.
  apply: fmon_eq_intro => n. by apply: H.
- move => X X' R /=. move => _ _ _.
  rewrite /Gr. by rewrite conv_PBot_simpl.
Defined.
End conversion.

Lemma fun2tree2fun_Cont (S : cppoType) (F : FuncType DA DB DC) (Hpure : isPure F) :
  @tree2funT (Cont S) (fun2tree F) =-= F (Cont S).
Proof.
rewrite /tree2funT /=.
apply: fcont_eq_intro => q.
apply: fcont_eq_intro => a.
suff H : Gr (conv q a) (F (Cont STree) Que Ans) (F (Cont S) q a).
  rewrite /Gr in H. rewrite -H. rewrite /conv /=. by apply: lub_eq_compat.
rewrite /isPure in Hpure.
have H := Hpure _ _ (TRacc1 q a) => {Hpure}.
apply: H.
- move => a1 a1' H.
  have Eq : q a1 =-= q a1'
    by apply: (fcont_eq_compat (Oeq_refl _)).
  move => h h' Hhh'. rewrite /Gr.
  have Eqh' : q a1 h' =-= q a1' h'
    by apply: (fcont_eq_compat Eq (Oeq_refl _)).
  apply: (Oeq_trans _ Eqh') => {Eq Eqh'}.
  by apply: conv_Que_simpl.
- move => c c' Hcc'. rewrite /Gr -Hcc'.
  by apply: conv_Ans_simpl.
Qed.

Definition Phi (T : monadType) (F : (DA -=> Cont (T DC) DB) =-> Cont (T DC) DC) : (DA -=> T DB) =-> T DC
  := Fcont_app F (@tval T DC) << CCOMP _ _ _ << <| const _ (@tbind T DB DC) , Id |>.

Definition PHI (T : monadType)
  : ((DA -=> Cont (T DC) DB) -=> Cont (T DC) DC) =-> (DA -=> T DB) -=> T DC
  := exp_fun (EV _ _ <<
     <| EV _ _ <<
        <|
         FST _ _,
         CCOMP _ _ _ << <| const _ (@tbind T DB DC), SND _ _ |>
        |>,
        const _ (@tval T DC)
     |>).

Lemma Phi_simpl (T : monadType) F g :
  Phi F g =-= F (tbind T _ _ << g) (tval T _).
Proof.
rewrite /=.
apply: fcont_eq_compat; last by apply: Oeq_refl.
by apply: fcont_eq_intro => a.
Qed.

Lemma PHI_simpl (T : monadType) F g :
  @PHI T F g =-= F (tbind T _ _ << g) (tval T _).
Proof.
by [].
Qed.

Definition TRacc2 (T : monadType) : TRelAccType (Cont (T DC)) T.
exists
  (fun (X X' : cpoType) (R : Rel X X') => fun (H : Cont (T DC) X) (H' : T X') =>
    forall h h', (R =R=> @IdR (T DC)) h h' ->
      (@IdR (T DC) (H h) (tbind T _ _ H' h'))).
- split.
  + intros. rewrite /IdR /=. rewrite taxiom0. by firstorder.
  + move => X X' Y Y' Q R f f' t t' H H0.
    move => h h' Hhh'. rewrite taxiom2 /=. apply: H => x x' Hxx' /=. by apply: H0.
- move => X X' R Hadm. move => c c' /= H.
  move => h h' Hhh'. rewrite lub_comp_eq. apply: lub_eq_compat.
  apply: fmon_eq_intro => n /=. by apply: H.
- move => X X' R /=. move => h h' _. by rewrite taxiom3.
Defined.

Lemma PHI_Cont (T : monadType) (F : FuncType DA DB DC) (Hpure : isPure F) :
  PHI T (F (Cont (T DC))) =-= F T.
Proof.
apply: fcont_eq_intro => g. rewrite PHI_simpl.
rewrite -(taxiom1 (F T g)).
have H := Hpure _ _ (TRacc2 T) => {Hpure}.
apply: H.
- move => a a' Haa'.
  have Eg : g a =-= g a' by apply: (fcont_eq_compat (Oeq_refl _)).
  move => h h' Hhh' /=.
  have Eh : h =-= h'
    by apply: fcont_eq_intro => b; apply: (Hhh' _ _ (Oeq_refl _)).
  by rewrite -Eg -Eh.
- move => c c' H. by rewrite H.
Qed.

Theorem fun2tree2fun (F : FuncType DA DB DC) (Hpure : isPure F) :
  forall (T : monadType), @tree2fun (fun2tree F) T =-= @F T.
Proof.
move => T.
rewrite -[in X in _ =-= X](@PHI_Cont _ F) => //.
rewrite -[in X in _ =-= X](@fun2tree2fun_Cont _ F) => //.
rewrite [in X in _ =-= X](@PHI_Cont _ (tree2fun (fun2tree F))) => //.
by apply: tree2fun_pure.
Qed.

