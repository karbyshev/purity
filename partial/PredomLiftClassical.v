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

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(*Section Utils.

Lemma lem00 D (x y : D _BOT) :
  (forall n, pred_nth x n = pred_nth y n) -> x =-= y.
Proof.
move => H. split => /=.
- apply: DLless_cond => d Ex.
  elim: (eqValpred Ex) => k [d' [Hx e]].
  have Hy : pred_nth y k = Val d' by rewrite -H.
  have Ey : y =-= Val d' by rewrite -Hy pred_nth_eq.
  rewrite Ex Ey. by apply: Val_le_compat; auto.
- apply: DLless_cond => d Ey.
  elim: (eqValpred Ey) => k [d' [Hy e]].
  have Hx : pred_nth x k = Val d' by rewrite H.
  have Ex : x =-= Val d' by rewrite -Hx pred_nth_eq.
  rewrite Ex Ey. by apply: Val_le_compat; auto.
Qed.

Lemma pred_nth_bot (A : cpoType) :
  forall n, pred_nth (PBot : A _BOT) n = PBot.
elim => [//= | n IH].
change (pred_nth (DL_bot A) n.+1 = PBot).
by rewrite DL_bot_eq /=.
Qed.

End Utils.*)

Lemma forallEps_eq_bot D (x : D _BOT) :
  (forall n, exists s, pred_nth x n = Eps s) -> x =-= PBot.
Proof.
move => H. split => /=; last by apply: leastP.
apply: DLless_cond => d Ex.
elim: (eqValpred Ex) => {d Ex} k [d' [Hx _]].
elim: (H k) => s. by rewrite Hx.
Qed.

Require Import Classical.

(* non-constructive axiom *)
Lemma axiom_liftCpo_dec D (x : D _BOT) :
  x =-= PBot \/ exists d, x =-= Val d.
Proof.
elim: (classic (forall n, exists s, pred_nth x n = Eps s)) => H.
- left. by apply: forallEps_eq_bot.
- right.
  have H1 := not_all_ex_not _ _ H.
  elim: H1 => {H} k H.
  elim: (isEps_dec (pred_nth x k)) => [[d Ex] | Hnot].
  - exists d. by rewrite -Ex pred_nth_eq.
  - destruct (pred_nth x k) => //.
    by have H1 : exists s0, Eps s = Eps s0 by eauto.
Qed.

Section Mu1.
Variable A : cpoType.
Variable B : cppoType.
Variable f : A =-> B.

Definition chainF (s : A _BOT) : natO -> B
  := fun n =>
       match (pred_nth s n) with
         | Eps s => PBot
         | Val d => f d
       end.

Definition chainF_mono s : monotonic (chainF s).
move => n m H.
rewrite /chainF.
case E : (pred_nth s n) => [sn | d].
- by apply: leastP.
- rewrite natO_le in H.
  have H1 := subnKC H. move/eqP : H1 => H1. rewrite eq_sym in H1.
  by rewrite (pred_nth_comp _ H1) E pred_nth_val.
Qed.

Definition ChainF (s : A _BOT) := Eval hnf in mk_fmono (@chainF_mono s).

Definition ChainF_lub (s : A _BOT) := lub (ChainF s).

Lemma ChainF_lub_bot (s : A _BOT) :
  s =-= PBot -> lub (ChainF s) =-= PBot.
Proof.
move => e. split; last by apply: leastP.
apply: lub_le => n /=.
rewrite /chainF.
elim: (isEps_dec (pred_nth s n)) => [[d P] | H].
- move: e => [le _]. rewrite /= in le.
  have H : DLle (Val d) s by apply: (DLleVal P).
  have Hfalse : DLle (Val d) PBot by apply: (Ole_trans H).
  by elim: (PBot_incon Hfalse).
- rewrite /isEps in H. by destruct (pred_nth s n).
Qed.

Lemma pred_nth_ChainF_lub (s : A _BOT) d n :
  pred_nth s n = Val d -> ChainF_lub s =-= f d.
Proof.
move => H.
rewrite /ChainF /= /chainF in H.
have H1 : mseq_lift_left (ChainF s) n =-= fmon_cte _ (f d).
  apply: fmon_eq_intro => m /=.
  rewrite /chainF. by rewrite pred_nth_sum H pred_nth_val.
rewrite /ChainF_lub. rewrite (lub_lift_left _ n). rewrite H1. by apply: lub_const.
Qed.

Lemma ChainF_lub_Val (s : A _BOT) d :
  s =-= Val d -> lub (ChainF s) =-= f d.
Proof.
move => e.
elim: (eqValpred e) => [n [d' [Hn Hdd']]].
have e' : s =-= Val d'
  by apply: (Oeq_trans e); apply: Val_eq_compat.
rewrite Hdd' => {e Hdd' d}. rename d' into d.
by apply: (pred_nth_ChainF_lub Hn).
Qed.

Lemma ChainF_lub_mono : monotonic (ChainF_lub).
Proof.
move => s1 s2 Hle.
rewrite /ChainF_lub.
case: (axiom_liftCpo_dec s1) => [e1 | [d1 e1]]. (* non-constructive step! *)
- rewrite (ChainF_lub_bot e1). by apply: leastP.
- case: (axiom_liftCpo_dec s2) => [e2 | [d2 e2]]. (* non-constructive step! *)
  + have Hfalse : DLle (Val d1) PBot.
      rewrite -e1 /=. apply: (Ole_trans Hle). by elim: e2.
    by elim: (PBot_incon Hfalse).
  + rewrite (ChainF_lub_Val e1). rewrite (ChainF_lub_Val e2).
    apply: fmonotonic. apply: DLleVal_leq.
    elim: e1 => _ e1. elim: e2 => e2 _.
    apply: (Ole_trans e1). by apply: (Ole_trans Hle).
Qed.

Definition ChainF_lub_mon := Eval hnf in mk_fmono (@ChainF_lub_mono).

Lemma lem01 D (c : natO =-> D _BOT) d (Hlubc : lub c =-= Val d) :
  exists k, exists dk,
    c k =-= Val dk /\ dk <= d /\
    exists c' : natO =-> D _BOT,
      c' = mseq_lift_left c k /\
      lub c' =-= Val d /\
      (forall i, exists d', c' i =-= Val d' /\
        dk <= d' /\ d' <= d) /\
      exists dc : natO =-> D,
        lub dc =-= d /\
        forall i, c' i =-= Val (dc i).
Proof.
elim: (lubval Hlubc) => k [dk [Hdk le]].
exists k. exists dk. split; [ | split] => //.
pose c' := mseq_lift_left c k. exists c'. split => //.
have Hlubc' : lub c' =-= Val d
  by rewrite /c' -lub_lift_left Hlubc.
split => //.
have H :
  forall i, exists d', c' i =-= Val d' /\ dk <= d' /\ d' <= d.
  move => i. rewrite /c' /mseq_lift_left /=.
  elim: (allvalsfromhere i Hdk) => d' [Hd' le'].
  exists d'. split; [ | split] => //.
  apply: vleinj. rewrite -Hd' -Hlubc'.
  change (c' i <= lub c'). by apply: le_lub.
split => //.
elim: (DLvalgetchain Hdk) => [dc Hdc].
exists dc.
split => //.
apply: vinj. change (eta (lub dc) =-= Val d).
rewrite lub_comp_eq. rewrite -Hlubc'.
apply: lub_eq_compat. apply: fmon_eq_intro => n /=.
by rewrite Hdc.
Qed.

Lemma ChainF_lub_cont : continuous (ChainF_lub_mon).
Proof.
move => c /=. rewrite /ChainF_lub.
case: (axiom_liftCpo_dec (lub c)) => [e | [d e]]. (* non-constructive step! *)
- rewrite (ChainF_lub_bot e). by apply: leastP.
- rewrite (ChainF_lub_Val e).
  elim: (lem01 e) => [k [dk [Hdk [ledk [c' [Hdefc' [Hlubc' [Hc' [dc [Hlubdc Hdc]]]]]]]]]].
  rewrite (lub_lift_left _ k).
  have H : mseq_lift_left (ChainF_lub_mon << c) k =-= (f : fmono _ _) << dc.
    apply: fmon_eq_intro => n /=.
    suff : (ChainF_lub (c' n) =-= f (dc n)); first by rewrite Hdefc'.
    by apply: (Oeq_trans (ChainF_lub_Val (Hdc n))).
  rewrite H => {H}.
  rewrite -lub_comp_eq. by rewrite Hlubdc.
Qed.

Definition mu1aux := Eval hnf in mk_fcont (@ChainF_lub_cont).
Definition mu1 := locked mu1aux.

Lemma mu1axiom1 : mu1 PBot =-= PBot.
Proof.
unlock mu1. rewrite /= /ChainF_lub.
by rewrite ChainF_lub_bot => //.
Qed.

Lemma mu1axiom2 d : mu1 (Val d) =-= f d.
Proof.
unlock mu1. rewrite /= /ChainF_lub.
by rewrite ChainF_lub_Val => //.
Qed.

End Mu1.

