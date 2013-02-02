Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import FunctionalExtensionality.
Set Automatic Coercions Import.
Require Import relations.
Require Import Relations.
Require Import Utf8.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Functional.
Variables A B C : Type.

Definition FuncType : Type :=
  forall S, (A -> State S B) -> State S C.
End Functional.

Section Purity.
Variables A B C : Type.

Definition isPure (F : FuncType A B C) : Prop
  := forall S S' (TRacc : StateTRaccType S S'),
       ((@IdR A =R=> (StateTR TRacc) _ _ (@IdR B)) =R=>
          (StateTR TRacc) _ _ (@IdR C)) (F S) (F S').
End Purity.

Section Strategy.

Variables A B C : Type.
Inductive Tree :=
  Ans : C -> Tree
| Que : A -> (B -> Tree) -> Tree.

Fixpoint tree2funT S (t : Tree) : (A -> State S B) -> State S C :=
  match t with
    | Ans c => fun k => valState c
    | Que a f =>
        fun k => bindState (k a) (fun b => tree2funT (f b) k)
  end.

Definition tree2fun (t : Tree) : FuncType A B C.
move => S. by apply: (tree2funT t).
Defined.

Lemma tree2fun_simpl (t : Tree) S : @tree2fun t S = tree2funT t.
Proof. by []. Qed.

Lemma tree2fun_pure (t : Tree) : isPure (@tree2fun t).
Proof.
rewrite /isPure.
elim: t => [| a f Hind].
- rewrite /ArrR /=.
  move => c S S' TRacc k k' H /=.
  by apply TRacc.
- rewrite /ArrR /=. rewrite /ArrR /= in Hind.
  move => S S' TRacc k k' H /=.
  eapply (proj2 (StateAcc TRacc)); first by eapply H.
  rewrite /ArrR => b b' /=; elim. by apply: Hind.
Qed.

Lemma tree2fun_Ans_simpl S (k : A -> State S B) d s :
  tree2fun (Ans d) k s = (d, s).
Proof. by []. Qed.

Lemma tree2fun_Que_simpl S (k : A -> State S B) a f b1 s s1 :
  k a s = (b1, s1) ->
  tree2fun (Que a f) k s = tree2fun (f b1) k s1.
Proof.
move => H.
rewrite /tree2fun /tree2funT /bindState /=.
by rewrite H.
Qed.

End Strategy.

Implicit Arguments Ans [A B C].
Implicit Arguments Que [A B C].

Parameters A B C : Type.
(* We assume that set B is not empty
   with botB being a destinguished element *)
Parameter botB : B.

Section TR0.
Variables S S' : Type.
Variable Inv : S -> Prop.
Variable Trans : relation (S * S').

Definition TR0 : StateTRtype S S'
  := fun X X' (R : Rel X X')
         (tx : State S X) (tx' : State S' X') =>
    forall s s',
      let (x, s1) := tx s in
      let (x',s1') := tx' s' in
        (exists u', R x u') /\ (exists u, R u x') /\
        (Inv s1 ->
          R x x' /\ Inv s /\ Trans (s,s') (s1,s1')).

Variable reflexiveTrans : reflexive _ Trans.
Variable transitiveTrans : transitive _ Trans.

Definition TR0acc : StateTRaccType S S'.
exists TR0.
split.
- move => X X' R x x' Hxx'.
  move => s s'. rewrite /valState /tval /=.
  by firstorder.
- move => X X' Y Y' Q R f f' t t' HQ Harr.
  move => s s'. rewrite /bindState /tbind /=.
  case E1 : (t s) => [x1 s1].
  case E1' : (t' s') => [x1' s1'].
  case E2 : (f x1 s1) => [x2 s2].
  move E2' : (f' x1' s1') => [x2' s2'].
  have Htmp := HQ s s'. rewrite E1 E1' in Htmp.
  case: Htmp => [[u1' H11] [[u1 H12] H13]].
  split; [| split ].
  + have Htmp := Harr _ _ H11 s1 s1'. rewrite E2 in Htmp.
    destruct (f' u1' s1'). by intuition.
  + have Htmp := Harr _ _ H12 s1 s1'. rewrite E2' in Htmp.
    destruct (f u1 s1). by intuition.
  + have H : Inv s2 -> Inv s1.
      have Htmp := Harr _ _ H11 s1 s1'. rewrite E2 in Htmp.
      destruct (f' u1' s1'). by intuition.
    move => Hinv.
    have HQ1 : Q x1 x1' by intuition.
    have Htmp := Harr _ _ HQ1 s1 s1'. rewrite E2 E2' in Htmp.
    by firstorder.
Defined.
End TR0.

(* Now, we prove that snapback is not pure *)

Record TestMini : Type
  := mkTestMini { calmini : bool }.

Definition initTestMini : TestMini := {| calmini := false |}.

Definition kTestMini : A -> State TestMini B := 
  fun _ _ => (botB, {| calmini := true |}).

Theorem snapback_is_not_pure
  (F : FuncType A B C) (Hpure : isPure F) S k s :
  let (c1',s1') := F TestMini kTestMini initTestMini in 
  let (c1, s1) := F S k s in
    s1'.(calmini) = false -> c1 = c1' /\ s = s1.
Proof.
pose Inv : TestMini -> Prop := fun s => s.(calmini) = false.
pose Tran : relation (TestMini * S)
  := fun (p1 p2 : TestMini * S) =>
       let (_,s1') := p1 in
       let (_,s2') := p2 in
         s1' = s2'.
have HreflTran : reflexive _ Tran
  by rewrite /Tran; move => [_ s0].
have HtransTran : transitive _ Tran
  by rewrite /Tran; move => [_ s1] [_ s2] [_ s3]; congruence.
pose TR := @TR0acc _ _ Inv Tran HreflTran HtransTran.
have Harr := Hpure _ _ TR.
have Hargs : (@IdR _ =R=> StateTR TR (@IdR _)) kTestMini k.
  move => a a'; elim => {a'}.
  rewrite /TR /= /TR0 /= /IdR.
  move => s0' s0.
  elim E : (k a s0) => [c s1].
  by intuition; eauto.
have H := Harr _ _ Hargs initTestMini s => {Harr}.
case E1' : (F TestMini kTestMini initTestMini) => [c' s1'].
case E1 : (F S k s) => [c s1].
rewrite E1 E1' in H.
elim: H => [_ [_ H]].
rewrite /= /Inv /IdR in H.
by intuition.
Qed.

(* The example of a more general acceptable monadic relation *)
Section TRinv.
Variables S S' : Type.
Variable BigInv : S -> Prop.
Variable SmallInv : S -> Prop.
Variable Trans : relation (S * S').

Definition TRinv : StateTRtype S S'
  := fun X X' (R : Rel X X')
         (tx : State S X) (tx' : State S' X') =>
    forall s s',
      let (x, s1) := tx s in
      let (x',s1') := tx' s' in
        (exists u', R x u') /\ (exists u, R u x') /\
        (BigInv s -> BigInv s1) /\
        (BigInv s -> SmallInv s1 ->
          R x x' /\ Trans (s,s') (s1,s1') /\ SmallInv s).

Variable reflexiveTrans : reflexive _ Trans.
Variable transitiveTrans : transitive _ Trans.

Definition TRinvacc : StateTRaccType S S'.
exists TRinv.
split.
- move => X X' R x x' Hxx'.
  move => s s'. rewrite /valState /tval /=.
  by firstorder.
- move => X X' Y Y' Q R f f' t t' HQ Harr.
  move => s s'. rewrite /bindState /tbind /=.
  case E1 : (t s) => [x1 s1].
  case E1' : (t' s') => [x1' s1'].
  case E2 : (f x1 s1) => [x2 s2].
  move E2' : (f' x1' s1') => [x2' s2'].
  have Htmp := HQ s s'. rewrite E1 E1' in Htmp.
  case: Htmp => [[u1' H11] [[u1 H12] H13]].
  split; [| split; [| split ]].
  + have Htmp := Harr _ _ H11 s1 s1'. rewrite E2 in Htmp.
    destruct (f' u1' s1'). by intuition.
  + have Htmp := Harr _ _ H12 s1 s1'. rewrite E2' in Htmp.
    destruct (f u1 s1). by intuition.
  + have H := Harr _ _ H11 s1 s1'. rewrite E2 in H.
    destruct (f' u1' s1'). by intuition.
  + have H : BigInv s -> SmallInv s2 -> SmallInv s1.
      have Htmp := Harr _ _ H11 s1 s1'. rewrite E2 in Htmp.
      destruct (f' u1' s1'). by intuition.
    move => Hbig Hsmall2.
    have HQ1 : Q x1 x1' by intuition.
    have Htmp := Harr _ _ HQ1 s1 s1'. rewrite E2 E2' in Htmp.
    by firstorder.
Defined.
End TRinv.

(* Another simple example *)
Section TRtrans.
Variable S S' : Type.
Variable Trans : relation S.
Variable Trans' : relation S'.

Definition TRtrans : StateTRtype S S' :=
  fun X X' (R : Rel X X') (tx : State S X) (tx' : State S' X') => 
    forall s s',
      let (x, s1) := tx s in 
      let (x',s1'):= tx' s' in 
        (exists u', R x u') /\ (exists u, R u x') /\
        (Trans s s1) /\ (Trans' s' s1').

Variable reflexiveTrans : reflexive _ Trans.
Variable transitiveTrans : transitive _ Trans.
Variable reflexiveTrans' : reflexive _ Trans'.
Variable transitiveTrans' : transitive _ Trans'.

Definition TRtransacc : StateTRaccType S S'.
exists TRtrans.
split.
- move => X X' R x x' Hxx'.
  move => s s'. rewrite /valState /tval /=.
  by firstorder.
- move => X X' Y Y' Q R f f' t t' HQ Harr.
  move => s s'. rewrite /bindState /tbind /=.
  case E1 : (t s) => [x1 s1].
  case E1' : (t' s') => [x1' s1'].
  case E2 : (f x1 s1) => [x2 s2].
  move E2' : (f' x1' s1') => [x2' s2'].
  have Htmp := HQ s s'. rewrite E1 E1' in Htmp.
  case: Htmp => [[u1' H11] [[u1 H12] [H13 H14]]].
  split; [| split; [| split]].
  + have Htmp := Harr _ _ H11 s1 s1'. rewrite E2 in Htmp.
    destruct (f' u1' s1'). by intuition.
  + have Htmp := Harr _ _ H12 s1 s1'. rewrite E2' in Htmp.
    destruct (f u1 s1). by intuition.
  + have H := Harr _ _ H11 s1 s1'. rewrite E2 in H.
    destruct (f' u1' s1').
    by apply: (transitiveTrans H13); intuition.
  + have H := Harr _ _ H12 s1 s1'. rewrite E2' in H.
    destruct (f u1 s1).
    by apply: (transitiveTrans' H14); intuition.
Defined.
End TRtrans.

Record TestSet := mkTest
  { arg : option A;
    que : seq A;
    ans : seq B }.

Definition initTest (bs : seq B) : TestSet :=
  {| arg := None;
     que := [::];
     ans := bs |}.

Definition kTest : A -> State TestSet B := 
  fun a s =>
    match s.(arg) with
      | Some _ => (botB, s)
      | None =>
          match s.(ans) with
            | [::] =>
                (botB, {| arg := Some a;
                          que := s.(que);
                          ans := [::] |})
            | b :: bs =>
                (b, {| arg := s.(arg);
                       que := s.(que) ++ [::a];
                       ans := bs |})
          end
    end.

Lemma tree2fun_kTest_cal (t : Tree A B C) s s1 r x :
  (r,s1) = tree2fun t kTest s ->
  s.(arg) = Some x ->
  s1 = s.
Proof.
move: s s1 r x.
elim: t => [c | a f IH].
- rewrite /= /valState /tval /=.
  by move => s s1 r x [_ ?]; subst.
- rewrite /= /bindState /tbind /=.
  move => s s2 r x.
  elim E: (kTest a s) => [b s1].
  move => H Harg.
  rewrite /kTest Harg in E. case: E => _ ?; subst s1.
  by apply: IH; eauto.
Qed.

Lemma lem_que_app_sim (F : FuncType A B C) (Hpure : isPure F)
        s s1 s' s1' c c' l :
  (c, s1) = F _ kTest s ->
  (c', s1') = F _ kTest s' ->
  s.(arg) = s'.(arg) ->
  s.(ans) = s'.(ans) ->
  l ++ s.(que) = s'.(que) ->
  c = c' /\
  s1.(arg) = s1'.(arg) /\
  s1.(ans) = s1'.(ans) /\
  l ++ s1.(que) = s1'.(que).
Proof.
pose R : relation TestSet
  := fun (s1 s1' : TestSet) =>
         s1.(arg) = s1'.(arg) /\
         s1.(ans) = s1'.(ans) /\
         l ++ s1.(que) = s1'.(que).
pose TR := TRparamAcc R.
have Harr := Hpure _ _ TR.
have Hargs : (@IdR _ =R=> StateTR TR (@IdR _)) kTest kTest.
  move => x x'; elim => {x'}.
  rewrite /TR /= /TRparam /=.
  move => ts ts' H /=.
  case E : (kTest x ts) => [x1 ts1].
  case E' : (kTest x ts') => [x1' ts1'].
  move: H => [Harg [Hans Hque]].
  rewrite /IdR /R /=.
  rewrite /kTest in E.
  rewrite /kTest in E'.
  rewrite -Harg -Hans -Hque in E'.
  move: E E'; case Earg: (arg ts) => [a |].
  + by case => ? ?; subst x1 ts1;
    case => ? ?; subst x1' ts1'.
  + case: (ans ts) => [| b bs].
    * by case => ? ?; subst x1 ts1;
      case => ? ?; subst x1' ts1'.
    * case => ? ?; subst x1 ts1.
      case => ? ?; subst x1' ts1'.
      by rewrite /= catA.
have Htmp := Harr _ _ Hargs s s' => {Harr Hargs}.
move => H H'. rewrite -H -H' in Htmp => {H H'}.
now firstorder.
Qed.


Section TR1gen.

Variable S S' : Type.
Variable Trans : relation S.
Variable Trans' : relation S'.
Variable StateInv : S -> S' -> Prop.

Definition TR1gen : StateTRtype S S' :=
  fun X X' (R : Rel X X') (tx : State S X) (tx' : State S' X') => 
    forall s s',
      let (x, s1) := tx s in
      let (x',s1'):= tx' s' in
        (exists u', R x u') /\ (exists u, R u x') /\
        (Trans s s1) /\ (Trans' s' s1') /\
        (StateInv s s' -> StateInv s1 s1' /\ R x x').

Variable reflexiveTrans : reflexive _ Trans.
Variable transitiveTrans : transitive _ Trans.
Variable reflexiveTrans' : reflexive _ Trans'.
Variable transitiveTrans' : transitive _ Trans'.

Definition TR1genacc : StateTRaccType S S'.
exists TR1gen.
split.
- move => X X' R x x' Hxx'.
  move => s s'. rewrite /valState /tval /=.
  by firstorder.
- move => X X' Y Y' Q R f f' t t' HQ Harr.
  move => s s'. rewrite /bindState /tbind /=.
  case E1 : (t s) => [x1 s1].
  case E1' : (t' s') => [x1' s1'].
  case E2 : (f x1 s1) => [x2 s2].
  move E2' : (f' x1' s1') => [x2' s2'].
  have Htmp := HQ s s'. rewrite E1 E1' in Htmp.
  case: Htmp => [[u1' H11] [[u1 H12] [H13 [H14 H15]]]].
  split; [| split; [| split; [| split ]]].
  + have Htmp := Harr _ _ H11 s1 s1'. rewrite E2 in Htmp.
    destruct (f' u1' s1'). by intuition.
  + have Htmp := Harr _ _ H12 s1 s1'. rewrite E2' in Htmp.
    destruct (f u1 s1). by intuition.
  + have H := Harr _ _ H11 s1 s1'. rewrite E2 in H.
    destruct (f' u1' s1').
    by apply: (transitiveTrans H13); intuition.
  + have H := Harr _ _ H12 s1 s1'. rewrite E2' in H.
    destruct (f u1 s1).
    by apply: (transitiveTrans' H14); intuition.
  + move => Hstate0.
    elim: (H15 Hstate0) => [Hstate1 Q1].
    have Htmp := Harr _ _ Q1 s1 s1'. rewrite E2 E2' in Htmp.
    by intuition.
Defined.
End TR1gen.

Lemma lem_Test_cal_ans (F : FuncType A B C) (Hpure : isPure F) :
  forall bs c r,
    F _ kTest (initTest bs) = (c,r) ->
    (exists a, r.(arg) = Some a) ->
    r.(ans) = [::].
Proof.
pose Trans : relation TestSet
  := fun r r1 =>
       (r.(arg) = None ->
        (exists a, r1.(arg) = Some a) -> r1.(ans) = [::]) /\
       (r.(ans) = [::] -> r1.(ans) = [::]).
have HreflTrans : reflexive _ Trans.
  move => r. rewrite /Trans. split => //.
  move => H [a Habs]; by rewrite H in Habs.
have HtransTrans : transitive _ Trans.
  rewrite /Trans => r1 r2 r3 H12 H23.
  split; last by intuition.
  move: H12 H23.
  case Earg : (arg r2) => [a |]; by intuition; eauto.
pose Trans' : relation TestSet := fun _ _ => True.
have HreflTrans' : reflexive _ Trans' by [].
have HtransTrans' : transitive _ Trans' by [].
pose Inv : relation TestSet := fun s s' => s = s'.
pose TR := @TR1genacc _ _ Trans Trans' Inv
            HreflTrans HtransTrans HreflTrans' HtransTrans'.
have Harr := Hpure _ _ TR.
have Hargs : (@IdR _ =R=> StateTR TR (@IdR _)) kTest kTest.
  move => x x'. elim => {x'}.
  rewrite /TR /= /TR1gen.
  move => s s'.
  case E1 : (kTest x s) => [x1 s1].
  case E1' : (kTest x s') => [x1' s1'].
  split; [| split; [| split; [| split ]]] => //.
  - by exists x1.
  - by exists x1'.
  - rewrite /Trans.
    rewrite /kTest in E1.
    split.
    + move => Harg; rewrite Harg in E1.
      move: E1; case: (ans s) => [| b bs] /=;
        by case => _ ?; subst s1; firstorder.
    + move => Hans.
      move: E1; case: (arg s) => [a |].
      * by case => _ ?; subst s1.
      * rewrite Hans. by case => _ ?; subst s1.
  - rewrite /Inv /IdR. move => ?; subst s'.
    by rewrite E1 in E1'; case: E1'.
move => bs c s Hf.
have Htmp := Harr _ _ Hargs (initTest bs) (initTest bs).
rewrite Hf in Htmp.
by firstorder.
Qed.

Lemma lem_Test_ans_que (F : FuncType A B C) (Hpure : isPure F) :
  forall bs c r,
    F _ kTest (initTest bs) = (c,r) ->
    exists ds,
      bs = ds ++ (r.(ans)) /\
      size r.(que) = size ds.
Proof.
pose Trans : relation TestSet
  := fun r r1 =>
       (exists bb aa,
          r.(ans) = bb ++ r1.(ans) /\
          r1.(que) = r.(que) ++ aa /\
          size bb = size aa).
have HreflTrans : reflexive _ Trans.
  move => r. rewrite /Trans.
  by exists [::], [::]; rewrite cats0.
have HtransTrans : transitive _ Trans.
  rewrite /Trans => s1 s2 s3 [ans1 [que1 [H11 [H12 H13]]]]
                             [ans2 [que2 [H21 [H22 H23]]]].
  exists (ans1 ++ ans2), (que1 ++ que2).
  by rewrite H11 H21 H22 H12 !catA !size_cat H13 H23.
pose Trans' : relation TestSet := fun _ _ => True.
have HreflTrans' : reflexive _ Trans' by [].
have HtransTrans' : transitive _ Trans' by [].
pose Inv : relation TestSet := fun s s' => s = s'.
pose TR := @TR1genacc _ _ Trans Trans' Inv
            HreflTrans HtransTrans HreflTrans' HtransTrans'.
have Harr := Hpure _ _ TR.
have Hargs : (@IdR _ =R=> StateTR TR (@IdR _)) kTest kTest.
  move => x x'. elim => {x'}.
  rewrite /TR /= /TR1gen.
  move => s s'.
  case E1 : (kTest x s) => [x1 s1].
  case E1' : (kTest x s') => [x1' s1'].
  split; [| split; [| split; [| split ]]] => //.
  - by exists x1.
  - by exists x1'.
  - rewrite /Trans.
    rewrite /kTest in E1.
    move: E1; case: (arg s) => [a |].
    + case => _ ?; subst s1.
      by exists [::], [::]; rewrite cats0.
    + case: (ans s) => [| b bs].
      * case => _ ?; subst s1 => /=.
        by exists [::], [::]; rewrite !cats0.
      * case => _ ?; subst s1 => /=.
        by exists [::b], [::x].
  - rewrite /Inv /IdR. move => ?; subst s'.
    by rewrite E1 in E1'; case: E1'.
move => bs c r Hf.
have Htmp := Harr _ _ Hargs (initTest bs) (initTest bs).
rewrite Hf in Htmp.
elim: Htmp => [_ [_ [H _]]].
clear - H.
rewrite /Trans /= in H.
case: H => [bb [aa H]].
exists bb. 
by firstorder; congruence.
Qed.

Inductive Fun2Tree (F : FuncType A B C)
  : seq B -> Tree A B C -> Prop :=
  | BaseCase :
      forall c l s0 s1, 
        s0 = initTest l /\
        (c, s1) = F _ kTest s0 /\
        s1.(arg) = None ->
        Fun2Tree F l (Ans c)
  | InductiveCase :
      forall a (cont : B -> Tree A B C) l s0 s1 v,
        s0 = initTest l /\
        (v, s1) = F _ kTest s0 /\
        s1.(arg) = Some a /\
        (forall b, Fun2Tree F (l ++ [::b]) (cont b)) ->
        Fun2Tree F l (Que a cont).

Lemma Fun2Tree_Ans_elim F l c :
  Fun2Tree F l (Ans c) ->
  exists s1, 
    (c, s1) = F _ kTest (initTest l) /\ s1.(arg) = None.
Proof.
move => H.
inversion H as [c0 l0 s0 s1 [H0 [H1 H2]] e1 e2 | ].
rewrite H0 in H1.
by exists s1.
Qed.

Lemma Fun2Tree_Que_elim F l a cont :
  Fun2Tree F l (Que a cont) ->
  exists s1, exists c,
    (c, s1) = F _ kTest (initTest l) /\
    s1.(arg) = Some a /\
    (forall b, Fun2Tree F (l ++ [:: b]) (cont b)).
Proof.
move => H.
inversion H as [| a0 cont0 l0 s0 s1 v [H1 [H2 H3]] e1 e2].
subst cont0 a0 l0.
rewrite H1 in H2 => {H1}.
by exists s1; exists v.
Qed.

(* The graph Fun2Tree is functional *)
Lemma Fun2Tree_functional (F : FuncType A B C) l t1 t2 :
  Fun2Tree F l t1 -> Fun2Tree F l t2 -> t1 = t2.
Proof.
move: l t2.
elim: t1 => [c1 | a1 k1 IH].
- move => l t2 H1.
  elim: (Fun2Tree_Ans_elim H1) => [r1 [H11 H12]] {H1}.
  case: t2 => [c2 | a2 k2] H2.
  + elim: (Fun2Tree_Ans_elim H2) => [r2 [H21 H22]] {H2}.
    rewrite -H11 in H21.
    by inversion_clear H21.
  + elim: (Fun2Tree_Que_elim H2) => r2 [c2 [H21 [H22 H23]]] {H2}.
    rewrite -H11 in H21.
    inversion H21; subst.
    by rewrite H12 in H22.
- move => l t2 H1.
  elim: (Fun2Tree_Que_elim H1) => r1 [c1 [H11 [H12 H13]]] {H1}.
  case: t2 => [c2 | a2 k2] H2.
  + elim: (Fun2Tree_Ans_elim H2) => [r2 [H21 H22]] {H2}.
    rewrite -H11 in H21.
    inversion H21; subst.
    by rewrite H12 in H22.
  + elim: (Fun2Tree_Que_elim H2) => r2 [c2 [H21 [H22 H23]]] {H2}.
    rewrite -H11 in H21.
    inversion H21; subst; clear H21.
    rewrite H12 in H22.
    inversion H22; subst; clear H22.
    have Hk : k1 = k2 by extensionality b; firstorder.
    by subst.
Qed.

Lemma TreeFunTree_Que a f b l t :
  Fun2Tree (tree2fun (f b)) l t ->
  Fun2Tree (tree2fun (Que a f)) (b :: l) t.
Proof.
move: a f b l.
elim: t => [c | a f IH].
- move => a f b l H.
  elim: (Fun2Tree_Ans_elim H) => s {H} [H H0].
  pose s1 := {| arg := s.(arg);
                que := a :: s.(que);
                ans := s.(ans) |}.
  apply: (@BaseCase _ _ _ (initTest (b :: l)) s1).
  split; [| split] => //.
  rewrite /= /bindState /tbind /=.
  elim H': (tree2fun (f b) kTest
             {| arg:=None; que:=[:: a]; ans:=l |}) => [c' s1'].
  symmetry in H'.
  have Htmp := lem_que_app_sim (tree2fun_pure _) H H'.
  have H1 : c = c' /\
            arg s = arg s1' /\
            ans s = ans s1' /\
            [::a] ++ que s = que s1'
    by apply: Htmp.
  move => {Htmp}.
  move: H1 => [? [Earg [Eans Eque]]]; subst c'.
  rewrite /s1.
  f_equal.
  rewrite /= in Eque.
  rewrite Earg Eans Eque. by destruct s1'.
- idtac.
  move => a1 f1 b l H.
  elim: (Fun2Tree_Que_elim H) => s {H} [c H].
  pose s1 := {| arg := s.(arg);
                que := a1 :: s.(que);
                ans := s.(ans) |}.
  apply: (@InductiveCase _ _ _ _ (initTest (b :: l)) s1 c).
  split => //.
  rewrite /= /bindState /tbind /=.
  split; [| split]; try easy; last first.
  + move => b1. by apply: IH; intuition.
  + case: H => [H _].
    elim H': (tree2fun (f1 b) kTest
               {| arg := None; que := [:: a1]; ans := l |}) => [c' s1'].
    symmetry in H'.
    have Htmp := lem_que_app_sim (tree2fun_pure _) H H'.
    have H1 : c = c' /\
            arg s = arg s1' /\
            ans s = ans s1' /\
            [::a1] ++ que s = que s1'
      by apply: Htmp.
    move => {Htmp}.
    move: H1 => [? [Earg [Eans Eque]]]; subst c'.
    rewrite /s1.
    f_equal.
    rewrite /= in Eque.
    rewrite Earg Eans Eque. by destruct s1'.
Qed.

(* First, we prove that fun2tree is an inverse of tree2fun *)
Lemma TreeFunTree (t : Tree A B C) :
  Fun2Tree (tree2fun t) [::] t.
Proof.
elim: t => [c | a f H].
- now apply: BaseCase.
- elim E : (tree2fun (f botB) kTest
              {| arg := Some a; que := [::]; ans := [::] |})
           => [r s].
  symmetry in E.
  apply: (@InductiveCase _ _ _ _ (initTest [::]) s r).
  split => //.
  rewrite /= /bindState /tbind /=.
  split; [| split] => //.
  + have e : s = {| arg := Some a; que := [::]; ans := [::] |}
      by apply: (tree2fun_kTest_cal E).
    now rewrite e.
  + move => b. now apply: TreeFunTree_Que.
Qed.


Section Matches.
Variable S : Type.

Inductive Matches (k : A -> State S B) :
  seq A -> seq B -> relation S :=
  | MatchesN : forall s, Matches k nil nil s s 
  | MatchesC : forall q v s qs vs s1 s2, 
      k q s1 = (v, s2) ->
      Matches k qs vs s s1 ->
      Matches k (qs ++ [::q]) (vs ++ [::v]) s s2.

Hint Constructors Matches.

Lemma MatN_elim k s s1 :
  Matches k nil nil s s1 -> s = s1.
Proof.
move => H. inversion H => //. by destruct qs.
Qed.

Lemma app_inj_tail X (l1 l2 : seq X) x1 x2 :
  l1 ++ [:: x1] = l2 ++ [:: x2] -> l1 = l2 /\ x1 = x2.
Proof.
move: x2 l2.
induction l1 as [| a1 l1 IHl1].
- move => x2 l2. case: l2 => /= [H |].
  + by inversion H.
  + move => a l; by case: l.
- move => x2. case => [| a2 l2].
  + by elim l1.
  + case; elim => H. split; try f_equal; by firstorder.
Qed.

Lemma MatC_elim k qs q vs v s s2 :
  Matches k (qs ++ [::q]) (vs ++ [::v]) s s2 ->
  exists s1,
    (k q s1 = (v, s2) /\ Matches k qs vs s s1).
Proof.
move => H. inversion H.
- by destruct qs.
- subst s0 s3.
  elim (app_inj_tail H0) => e1 e2 {H0}. subst.
  elim (app_inj_tail H1) => e1 e2 {H1}. subst.
  by eauto.
Qed.

Lemma Mat_size k qs vs s s1 :
  Matches k qs vs s s1 -> size qs = size vs.
Proof.
elim => [// | {qs vs s s1} q v _ qs vs _ _ _ _ H].
by rewrite !size_cat H.
Qed.

Lemma Mat_nil1 k qs vs s s1 :
  Matches k qs vs s s1 -> qs = nil -> vs = nil.
Proof.
move => H Hq. have Htmp := Mat_size H.
rewrite Hq /= in Htmp. by apply: size0nil.
Qed.

Lemma Mat_nil2 k qs vs s s1 :
  Matches k qs vs s s1 -> vs = nil -> qs = nil.
Proof.
move => H Hv. have Htmp := Mat_size H.
rewrite Hv /= in Htmp. by apply: size0nil.
Qed.

Lemma Mat_cat_ans_nil k qs vs vs1 s0 s1 s2 :
  Matches k qs vs s0 s1 ->
  Matches k qs (vs ++ vs1) s0 s2 ->
  vs1 = nil.
Proof.
move => H1 H2.
have Hsize1 := Mat_size H1.
have Hsize2 := Mat_size H2.
rewrite size_cat in Hsize2.
apply: size0nil.
apply/eqP; rewrite -(eqn_add2l (size vs)); apply/eqP.
by rewrite -Hsize2 Hsize1.
Qed.

Lemma Mat_inj1 k qs vs s0 s1 s2 :
  Matches k qs vs s0 s1 -> 
  Matches k qs vs s0 s2 -> 
  s1 = s2.
Proof.
move => H. move: s2. elim: H.
- move => {qs vs s0 s1} s s2. move => H.
  inversion H as [| ? ? ? qs vs] => //. by destruct qs.
- move => {qs vs s0 s1} q v s qs vs s1 s2 E H IH.
  move => s3 Hcons.  
  inversion Hcons.
  + by destruct qs.
  + elim (app_inj_tail H0). move => e1 e2. subst qs0 q0.
    elim (app_inj_tail H1). move => e1 e2. subst vs0 v0.
    move => {H0 H1}.
    have Htmp : s1 = s4 by apply: IH. subst s4.
    by rewrite E in H2; case: H2.
Qed.

Lemma Mat_cat_ans k qs vs vs1 s0 s1 s2 :
  Matches k qs vs s0 s1 ->
  Matches k qs (vs ++ vs1) s0 s2 ->
  s1 = s2.
Proof.
move => H1 H2.
have Htmp : vs1 = nil by apply: (Mat_cat_ans_nil H1 H2).
rewrite Htmp cats0 in H2.
by apply: (Mat_inj1 H1 H2).
Qed.

Lemma Mat_cat_exists k que1 que2 ans1 ans2 s s2 :
  Matches k (que1 ++ que2) (ans1 ++ ans2) s s2 ->
  size que1 = size ans1 ->
  exists s1, Matches k que1 ans1 s s1.
Proof.
move: ans2 que1 ans1.
elim: que2 => [| q qs IH].
- case => [| b bs].
  + move => que1 ans1. by rewrite !cats0; eauto.
  + move => que1 ans1 H Hsize1.
    have H1 := Mat_size H.
    rewrite !size_cat Hsize1 /= in H1.
    move/eqP : H1. by rewrite eqn_add2l.
- case => [| b bs].
  + move => que1 ans1 H Hsize1.
    have H1 := Mat_size H.
    rewrite !size_cat Hsize1 /= in H1.
    move/eqP : H1. by rewrite eqn_add2l.
  + move => que1 ans1 H Hsize1.
    rewrite -!cat_rcons in H.
    have Hsize2 : size (rcons que1 q) = size (rcons ans1 b)
      by rewrite !size_rcons Hsize1.
    move => {Hsize1}.
    have H1 := IH _ _ _ H Hsize2.
    move => {IH H Hsize2}.
    elim: H1 => [ss H].
    rewrite -!cats1 in H.
    elim: (MatC_elim H) => s1 [H1 H2].
    by firstorder.
Qed.

Lemma Mat_cat k que1 que2 ans1 ans2 s s1 s2 :
  Matches k (que1 ++ que2) (ans1 ++ ans2) s s2 -> 
  Matches k que1 ans1 s s1 ->
  Matches k que2 ans2 s1 s2.
Proof.
move: ans2 que1 ans1 s2.
elim/last_ind : que2 => [| qs q IH].
- case => [| b bs ].
  + move => que1 ans1 s2. rewrite cats0. move => H2 H1.
    have E : s1 = s2 by apply: (Mat_cat_ans H1 H2).
    rewrite E. by constructor.
  + move => que1 ans1 s2 H2 H1.
    have Hsize1 := Mat_size H1.
    have Hsize2 := Mat_size H2.
    move/eqP : Hsize2.
    by rewrite !size_cat Hsize1 eqn_add2l.
- elim/last_ind => [| bs b _ ].
  + move => {IH} que1 ans1 s2 H2 H1.
    have Hsize1 := Mat_size H1.
    have Hsize2 := Mat_size H2.
    move/eqP : Hsize2.
    by rewrite !size_cat size_rcons Hsize1 eqn_add2l.
  + move => que1 ans1 s2.
    move => H2 H1.
    rewrite -!cats1.
    rewrite -!rcons_cat -!cats1 in H2.
    elim: (MatC_elim H2) => s1' [E H].
    have Htmp := (IH _ _ _ _ H H1); move => {IH H H1}.
    by apply: MatchesC; eauto.
Qed.

Lemma Mat_trans k que1 que2 ans1 ans2 s s1 s2 :
  Matches k que1 ans1 s s1 ->
  Matches k que2 ans2 s1 s2 -> 
  Matches k (que1 ++ que2) (ans1 ++ ans2) s s2.
Proof.
move => H1 H2. move: H1. elim: H2.
- by rewrite !cats0.
- move => {que2 ans2 s1 s2} a b s1 que2 ans2 s2 s3 e H2 IH H1.
  have H := IH H1. move => {H1 H2 IH}.
  rewrite !catA.
  by apply: MatchesC; eauto.
Qed.  

End Matches.


(* An even more general construction of an
   acceptable monadic relations with rely/guarantee conditions *)
Section TR2gen.
Variable S S' : Type.
Variable Trans : relation S.
Variable Trans' : relation S'.
Variable Rely : relation (S * S').
Variable Guar : relation (S * S').

Definition TR2gen : StateTRtype S S' :=
  fun X X' (R : Rel X X') (tx : State S X) (tx' : State S' X') => 
    forall s s',
      let (x, s1) := tx s in 
      let (x',s1'):= tx' s' in 
        (exists u', R x u') /\ (exists u, R u x') /\
        (Trans s s1) /\ (Trans' s' s1') /\
        (Rely (s, s') (s1, s1') ->
          (*Trans s s1 -> Trans' s' s1' ->*)
          R x x' /\ Guar (s, s') (s1, s1')).

Variable reflexiveTrans : reflexive _ Trans.
Variable transitiveTrans : transitive _ Trans.
Variable reflexiveTrans' : reflexive _ Trans'.
Variable transitiveTrans' : transitive _ Trans'.
Variable reflexiveGuar : reflexive _ Guar.
Variable transitiveGuar : transitive _ Guar.
Definition antitransitiveRelyGuar :=
  forall s s' s1 s1'  s2 s2',
    Rely (s,s') (s2,s2') ->
    Trans s s1 -> Trans s1 s2 ->
    Trans' s' s1' -> Trans' s1' s2' ->
    Rely (s,s') (s1,s1') /\
    (Guar (s,s') (s1,s1') ->  Rely (s1,s1') (s2,s2')).
Variable antitransitiveRely : antitransitiveRelyGuar.

Definition TR2genacc : StateTRaccType S S'.
exists TR2gen.
split.
- move => X X' R x x' Hxx'.
  move => s s'. rewrite /valState /tval /=.
  by firstorder.
- move => X X' Y Y' Q R f f' t t' HQ Harr.
  move => s s'. rewrite /bindState /tbind /=.
  case E1 : (t s) => [x1 s1].
  case E1' : (t' s') => [x1' s1'].
  case E2 : (f x1 s1) => [x2 s2].
  move E2' : (f' x1' s1') => [x2' s2'].
  have Htmp := HQ s s'. rewrite E1 E1' in Htmp.
  case: Htmp => [[u1' H11] [[u1 H12] [H13 [H14 H15]]]].
  have Htran2 : Trans s s2.
    have H := Harr _ _ H11 s1 s1'. rewrite E2 in H.
    destruct (f' u1' s1').
    by apply: (transitiveTrans H13); intuition.
  have Htran2' : Trans' s' s2'.
    have H := Harr _ _ H12 s1 s1'. rewrite E2' in H.
    destruct (f u1 s1).
    by apply: (transitiveTrans' H14); intuition.
  split; [ | split; [ | split; [ | split]]] => //.
  + have Htmp := Harr _ _ H11 s1 s1'. rewrite E2 in Htmp.
    destruct (f' u1' s1'). by intuition.
  + have Htmp := Harr _ _ H12 s1 s1'. rewrite E2' in Htmp.
    destruct (f u1 s1). by intuition.
  + have H : Rely (s,s') (s2,s2') -> Rely (s,s') (s1,s1') /\ Rely (s1,s1') (s2,s2').
      have Htmp := Harr _ _ H11 s1 s1'. rewrite E2 in Htmp.
      destruct (f' u1' s1').
      have Htmp' := Harr _ _ H12 s1 s1'.
      rewrite E2' in Htmp'.
      destruct (f u1 s1).
      move => Hrely.
      have H := @antitransitiveRely _ _ s1 s1' s2 s2' Hrely.
      by intuition.
    move => Hrely2.
    have HQ1 : Q x1 x1' by intuition. move => {H11 H12}.
    have Htmp := Harr _ _ HQ1 s1 s1'. rewrite E2 E2' in Htmp.
    by firstorder.
Defined.
End TR2gen.


Definition TransPre :=
  fun (ts ts1 : TestSet) (que1 : seq A) (ans1 : seq B) =>
    ts1.(arg) = None ->
    ts.(arg) = None /\
    size que1 = size ans1 /\
    ts1.(que) = ts.(que) ++ que1 /\
    ts.(ans) = ans1 ++ ts1.(ans).

Lemma TransPre_refl : forall ts, TransPre ts ts nil nil.
Proof.
move => s. by rewrite /TransPre cat0s cats0.
Qed.

Lemma TransPre_trans : forall ts ts1 ts2 que1 que2 ans1 ans2,
  TransPre ts ts1 que1 ans1 ->
  TransPre ts1 ts2 que2 ans2 -> 
  TransPre ts ts2 (que1 ++ que2) (ans1 ++ ans2).
Proof.
move => s s1 s2 q1 q2 a1 a2 T1 T2.
rewrite /TransPre. move => H.
elim: (T2 H) => e21 [e22 [e23 e24]].
elim: (T1 e21) => e11 [e12 [e13 e14]].
split; [| split; [| split]] => //.
- by rewrite !size_cat e12 e22.
- by rewrite e23 e13 catA.
- by rewrite e14 e24 catA.
Qed.

Lemma app_inv_head T :
  forall (l l1 l2 : seq T), l ++ l1 = l ++ l2 -> l1 = l2.
Proof.
elim => [// | a t IH].
move => l1 l2. rewrite !cat_cons. by case; intuition.
Qed.

Lemma app_inv_tail T :
  forall l l1 l2 : seq T, l1 ++ l = l2 ++ l -> l1 = l2.
Proof.
elim/last_ind => [| a t IH].
- move => l1 l2; by rewrite !cats0.
- move => l1 l2. rewrite -!rcons_cat -!cats1.
  move => H. elim (app_inj_tail H). by intuition.
Qed.

Lemma TransPre_inj : forall ts ts1 que1 que2 ans1 ans2,
  ts1.(arg) = None ->
  TransPre ts ts1 que1 ans1 ->
  TransPre ts ts1 que2 ans2 ->
  que1 = que2 /\ ans1 = ans2.
Proof.
move => s s1 q1 q2 a1 a2 H T1 T2.
elim: (T1 H) => e11 [e12 [e13 e14]].
elim: (T2 H) => e21 [e22 [e23 e24]].
split.
- apply: (@app_inv_head A s.(que)). by rewrite -e13 -e23.
- apply: (@app_inv_tail B s1.(ans)). by rewrite -e14 -e24.
Qed.

Lemma seq_size_ind T (P : seq T -> Type) :
  P [::] ->
  (forall n,
    (forall l, size l = n -> P l) ->
    forall l, size l = n.+1 -> P l) ->
  forall n l, size l = n -> P l.
Proof.
move => Pnil Ps. elim => [| n IH].
- move => l H. by rewrite [X in P X]size0nil.
- by apply: Ps.
Qed.

Lemma seq_tail_dest T l :
  {x : T & {hs | l = hs ++ [:: x]}} + {l = [::]}.
Proof.
elim: l => [ | a l IH]; try tauto.
case: IH => H; last first.
- left. rewrite H /=. by exists a; exists nil.
- left. elim: H => [a1 [l1 H1]]. rewrite H1 -cat_cons.
  by exists a1; exists (a :: l1).
Qed.

Lemma destruct_seq T l :
  {x : T & {tl | l = x :: tl}} + {l = [::]}.
Proof.
case: l.
- by intuition.
- move => h tl. left. by exists h; exists tl.
Qed.

Lemma LemBaseCase (F : FuncType A B C) (Hpure : isPure F) S k :
  forall ds ts res s s1 s2 v,
    F TestSet kTest (initTest ds) = (res, ts) ->
    Matches k ts.(que) ds s s1 ->
    ts.(arg) = None ->
    F S k s = (v, s2) -> v = res /\ s2 = s1.
Proof.
pose Trans : relation TestSet := fun ts ts1 =>
  exists que, exists ans, TransPre ts ts1 que ans.
have HreflTrans : reflexive _ Trans.
  move => p. rewrite /Trans /TransPre.
  by exists nil; exists nil; rewrite !cat0s !cats0.
have HtransTrans : transitive _ Trans.
  move => p1 p2 p3 [q1 [a1 H1]] [q2 [a2 H2]].
  rewrite /Trans.
  exists (q1 ++ q2); exists (a1 ++ a2).
  by apply: TransPre_trans; eauto.
pose Trans' : relation S := fun s s1 => True.
have HreflTrans' : reflexive _ Trans' by [].
have HtransTrans' : transitive _ Trans' by [].
pose Guar : relation (TestSet * S) := fun (p p' : TestSet * S) =>
  let (ts, s) := p in
  let (ts1, s1) := p' in
    exists que ans,
      TransPre ts ts1 que ans /\ Matches k que ans s s1.
have HreflGuar : reflexive _ Guar.
  elim => [tss ss]. rewrite /Guar.
  exists nil, nil.
  split; [by apply: TransPre_refl | by constructor].
have HtransGuar : transitive _ Guar.
  move => [tss1 ss1] [tss2 ss2] [tss3 ss3] [q1 [a1 [H11 H12]]] [q2 [a2 [H21 H22]]].
  exists (q1 ++ q2), (a1 ++ a2).
  split.
  - by apply: TransPre_trans; eauto.
  - by apply: Mat_trans; eauto.
pose Rely : relation (TestSet * S) := fun (p p' : TestSet * S) => 
  let (ts, s) := p in
  let (ts1, s1) := p' in 
    ts1.(arg) = None /\
    forall que ans, TransPre ts ts1 que ans ->
      exists s1, Matches k que ans s s1.
have HantitransRely : @antitransitiveRelyGuar _ _ Trans Trans' Rely Guar.
  move => tss0 ss0 tss1 ss1 tss2 ss2 Hrely2 Htran1 Htran2 _ _.
  have Hrely1 : Rely (tss0, ss0) (tss1, ss1).
    elim: Hrely2 => Hcal2 Himp2.
    elim: Htran2 => q2 [a2 Htran2].
    have Hcal1 : tss1.(arg) = None by firstorder.
    split; first by [].
    - move => q11 a11 H11.
      elim: Htran1 => q1 [a1 Htran1].
      elim: (TransPre_inj Hcal1 H11 Htran1) => e1 e2.
      rewrite e1 e2 => {H11 e1 e2}.
      have Htran := TransPre_trans Htran1 Htran2.
      elim: (Himp2 _ _ Htran) => s3 Hmat3.
      apply: (Mat_cat_exists Hmat3).
      + by firstorder.
  split; first by [].
  - move => Hguar1.
    have Hcal2 : tss2.(arg) = None by firstorder.
    have Hcal1 : tss1.(arg) = None by firstorder.
    split; first by [].
    move => q22 a22 H22.
    rewrite /Trans in Htran2.
    elim: Htran2 => q2 [a2 Htran2].
    elim: (TransPre_inj Hcal2 H22 Htran2) => e1 e2.
    rewrite e1 e2 => {H22 e1 e2}.
    rewrite /Rely in Hrely2.
    rewrite /Rely in Hrely1.
    elim: Hrely2 => _ Hrely2.
    elim: Hrely1 => _ Hrely1.
    elim: Htran1 => q1 [a1 Htran1].
    rewrite /Guar in Hguar1.
    have Htran : TransPre tss0 tss2 (q1 ++ q2) (a1 ++ a2)
      by apply: TransPre_trans; eauto.
    elim: (Hrely2 _ _ Htran) => ss2' Hmat2'.
    elim: Hguar1 => [q1' [a1' [Htran1' Hmat1']]].
    elim: (TransPre_inj Hcal1 Htran1' Htran1) => e1 e2.
    rewrite e1 e2 in Hmat1' => {e1 e2 Htran1'}.
    move: Hmat1' => Hmat1.
    exists ss2'.
    by apply: Mat_cat; eauto.
pose TR2 := @TR2genacc _ _ Trans Trans' Rely Guar HreflTrans HtransTrans HreflTrans' HtransTrans' HreflGuar HtransGuar HantitransRely.
have Harr := Hpure _ _ TR2.
have Hargs : (@IdR _ =R=> StateTR TR2 (@IdR _)) kTest k.
  move => x x'. elim. rewrite /TR2 /= /TR2gen.
  move => ts0 ss0.
  move E : (kTest x ts0) => p. move: E; case: p => xx1 ts1 E1.
  move E : (k x ss0) => p. move: E; case: p => xx1' ss1 E1'.
  have Htran1 : Trans ts0 ts1.
    rewrite /Trans.
    exists [::x]. exists [::xx1].
    rewrite /TransPre.
    move => H. rewrite /kTest in E1.
    case e : (ts0.(arg)) => [a |].
    - rewrite e in E1. case: E1 => _ e2. rewrite e2 in e.
      by rewrite e in H.
    - rewrite e in E1.
      case Ea : (ts0.(ans)) => [| aa aas ].
      + rewrite Ea in E1 => {Ea}. case: E1 => _ e2.
        by rewrite -e2 in H.
      + rewrite Ea in E1. case: E1 => e1 e2. by rewrite e1 -e2 /=.
  split; [| split; [| split; [| split ]]] => //.
  - by exists xx1.
  - by exists xx1'.
  - move => Hrely1. rewrite /Rely in Hrely1.
    elim: Hrely1 => Hcal1 Hrely1.
    have Hcal0 : ts0.(arg) = None by firstorder.
    have Ektest := E1. move: E1' => Ek.
    rewrite /kTest Hcal0 in E1.
    rewrite /Trans in Htran1. elim: Htran1 => [q1 [a1 Htran1]].
    case Ea : (ts0.(ans)) => [| aa aas].
    + rewrite Ea in E1. case: E1 => _ e2. by rewrite -e2 in Hcal1.
    + rewrite Ea in E1. case: E1 => e1 e2.
      rewrite e1 in Ea => {e1}.
      move: (Htran1 Hcal1) => Htmp.
      rewrite -e2 /= in Htmp.
      elim: Htmp => [_ [Hsize [Eqs Ea2]]].
      rewrite -cat1s Ea2 in Ea.
      move: (app_inv_tail Ea) => {Ea} Ea.
      subst a1. rewrite /= in Hsize.
      have Htmp : exists q, q1 = [::q].
        elim: (destruct_seq q1) => [[h [t H]] |];
          last by move => e; rewrite e in Hsize.
        rewrite H /= in Hsize.
        rewrite (size0nil (eq_add_S _ _ Hsize)) in H.
        by exists h.
      elim: Htmp => q ?. subst q1. move => {Hsize}.
      have Htmp := (app_inv_head Eqs).
      case: Htmp => ?. subst q. move => {Eqs}.
      elim: (Hrely1 _ _ Htran1) => [ss1' Hmat'].
      have Htmp := Hmat'.
      rewrite -[X in Matches _ X _]cat0s in Htmp.
      rewrite -[X in Matches _ _ X]cat0s in Htmp.
      elim: (MatC_elim Htmp) => {Htmp} ss0' [Hkss0' Hmat0].
      have E0 := (MatN_elim Hmat0). subst ss0'. move => {Hmat0}.
      rewrite Hkss0' in Ek. move => {Hkss0'}.
      case: Ek. move => ? ?. subst xx1' ss1'.
      split; first by [].
      rewrite /Guar. by exists [:: x], [:: xx1].
move => ds ts res s s1 s2 v Hf Hmat Ecal Hres.
have Htmp := Harr _ _ Hargs (initTest ds) s => {Harr Hargs}.
rewrite Hf Hres in Htmp.
elim: Htmp => [_ [_ [Htrans [_ Himp]]]].
elim: (Htrans) => qqs [aas Htranpre].
have Hrely : Rely (initTest ds, s) (ts, s2).
  rewrite /Rely.
  split => [// | qqs' aas' Htran' ].
  elim: (TransPre_inj Ecal Htranpre Htran') => e1 e2.
  subst qqs'; subst aas'. move => {Htran'}.
  exists s1.
  have Htmp := Htranpre Ecal. rewrite /= in Htmp.
  elim: Htmp => [_ [e1 [e2 e3]]].
  rewrite -e2.
  have Hats : ts.(ans) = nil.
    apply: size0nil.
    have H := Mat_size Hmat.
    rewrite e3 e2 e1 size_cat addnC in H.
    symmetry.
    apply/eqP. move/eqP : H. by rewrite (eqn_add2r (size aas) 0).
  rewrite Hats cats0 in e3.
  by rewrite -e3.
split.
- by firstorder.
- rewrite /Guar in Himp.
  elim: (Himp Hrely) => _ [qqs' [aas' [Htranpre' Hmat']]].
  elim: (TransPre_inj Ecal Htranpre Htranpre') => e1 e2.
  subst qqs'; subst aas'. move => {Htranpre'}.
  rewrite /TransPre /= in Htranpre.
  elim: (Htranpre Ecal) => [_ [e1 [e2 e3]]].
  have Hats : ts.(ans) = nil.
    apply: size0nil.
    have H := Mat_size Hmat.
    rewrite e3 e2 e1 size_cat addnC in H.
    symmetry.
    apply/eqP. move/eqP : H. by rewrite (eqn_add2r (size aas) 0).
  rewrite Hats cats0 in e3.
  rewrite -e2 -e3 in Hmat'.
  by apply: (Mat_inj1 Hmat' Hmat).
Qed.

(* TR3 is a generalization of TR1
   with an extra disjunction part State2 *)
Section TR3gen.

Variable S S' : Type.
Variable Trans : relation S.
Variable Trans' : relation S'.
Variable State1 : S -> S' -> Prop.
Variable State2 : S -> S' -> Prop.

Definition TR3gen : StateTRtype S S' :=
  fun X X' (R : Rel X X') (tx : State S X) (tx' : State S' X') => 
    forall s s',
      let (x, s1) := tx s in 
      let (x',s1'):= tx' s' in 
        (exists u', R x u') /\ (exists u, R u x') /\
        (Trans s s1) /\ (Trans' s' s1') /\ 
        (State1 s s' -> State1 s1 s1' /\ R x x' \/ State2 s1 s1').

Variable reflexiveTrans : reflexive _ Trans.
Variable transitiveTrans : transitive _ Trans.
Variable reflexiveTrans' : reflexive _ Trans'.
Variable transitiveTrans' : transitive _ Trans'.
Definition stepTransState2 :=
  forall s s' s1 s1',
    State2 s s' -> Trans s s1 -> Trans' s' s1' -> State2 s1 s1'.
Variable stepState2 : stepTransState2.

Definition TR3genacc : StateTRaccType S S'.
exists TR3gen.
split.
- move => X X' R x x' Hxx'.
  move => s s'. rewrite /valState /tval /=.
  by firstorder.
- move => X X' Y Y' Q R f f' t t' HQ Harr.
  move => s s'. rewrite /bindState /tbind /=.
  case E1 : (t s) => [x1 s1].
  case E1' : (t' s') => [x1' s1'].
  case E2 : (f x1 s1) => [x2 s2].
  move E2' : (f' x1' s1') => [x2' s2'].
  have Htmp := HQ s s'. rewrite E1 E1' in Htmp.
  case: Htmp => [[u1' H11] [[u1 H12] [H13 [H14 H15]]]].
  split; [| split; [| split; [| split ]]].
  + have Htmp := Harr _ _ H11 s1 s1'. rewrite E2 in Htmp.
    destruct (f' u1' s1'). by intuition.
  + have Htmp := Harr _ _ H12 s1 s1'. rewrite E2' in Htmp.
    destruct (f u1 s1). by intuition.
  + have H := Harr _ _ H11 s1 s1'. rewrite E2 in H.
    destruct (f' u1' s1').
    by apply: (transitiveTrans H13); intuition.
  + have H := Harr _ _ H12 s1 s1'. rewrite E2' in H.
    destruct (f u1 s1).
    by apply: (transitiveTrans' H14); intuition.
  + move => Hstate10.
    elim: (H15 Hstate10) => [[Hstate11 Q1] | Hstate21 ].
    * have Htmp := Harr _ _ Q1 s1 s1'. rewrite E2 E2' in Htmp.
      by intuition.
    * have Htran12 : Trans s1 s2.
        have Htmp := Harr _ _ H11 s1 s1'.
        rewrite E2 in Htmp. destruct (f' u1' s1').
        by intuition.
      have Htran12' : Trans' s1' s2'.
        have Htmp := Harr _ _ H12 s1 s1'.
        rewrite E2' in Htmp. destruct (f u1 s1).
        by intuition.
      right. by apply: (stepState2 Hstate21).
Defined.
End TR3gen.


Lemma LemStepCase (F : FuncType A B C) (Hpure : isPure F) :
  forall bs b a ts res ts1 res1,
    F TestSet kTest (initTest bs) = (res, ts) ->
    ts.(arg) = Some a ->
    F TestSet kTest (initTest (bs ++ [::b])) = (res1, ts1) ->
    ts1.(que) = ts.(que) ++ [::a].
Proof.
move => bs b.
pose Trans : relation TestSet := fun ts ts1 =>
  (ts1.(arg) = None -> ts.(arg) = None) /\
  ((exists a, ts.(arg) = Some a) -> ts = ts1) /\
  (ts.(ans) = nil ->
    ts = ts1 \/
    ts1.(ans) = nil /\ (exists a, ts1.(arg) = Some a) /\ ts1.(que) = ts.(que)).
have HreflTrans : reflexive _ Trans.
  move => tss. rewrite /Trans. by intuition.
have HtransTrans : transitive _ Trans.
  move => tss1 tss2 tss3 H12 H23.
  rewrite /Trans. rewrite /Trans in H12. rewrite /Trans in H23.
  split; [| split ].
  - by intuition.
  - move => Hcal1.
    have E12 : tss1 = tss2 by intuition.
    rewrite E12. by rewrite E12 in Hcal1; intuition.
  - move => Hans1.
    elim: H12 => [H11 [H12 H13]].
    elim: H23 => [H21 [H22 H23]].
    elim: (H13 Hans1) => [E12 | [H1 [H2 H3]]].
    + have Hans2 := Hans1. rewrite E12 in Hans2.
      elim: (H23 Hans2) => [E13 | H].
      * left. by rewrite E12.
      * right. by rewrite E12.
    + elim: (H23 H1) => [E13 | H].
      * right. rewrite -E13. by intuition.
      * right. rewrite -H3. by intuition.
pose Trans' := Trans.
have HreflTrans' := HreflTrans.
have HtransTrans' := HtransTrans.
pose State1 : TestSet -> TestSet -> Prop := fun ts ts' =>
  ts.(arg) = None /\ ts'.(arg) = None /\ 
  ts'.(ans) = ts.(ans) ++ [:: b] /\ 
  ts'.(que) = ts.(que).
pose State2 : TestSet -> TestSet -> Prop := fun ts ts' =>
  exists a,
    ts.(arg) = Some a /\ 
    ts.(ans) = nil /\
    ts'.(ans) = nil /\
    (ts'.(que) = ts.(que) ++ [:: a] /\ ts'.(ans) = nil).
have Hstep2 : stepTransState2 Trans Trans' State2.
  move => tss tss' tss1 tss1' Hstate2 Htran Htran'.
  rewrite /State2. rewrite /State2 in Hstate2.
  rewrite /Trans in Htran. rewrite /Trans' /Trans in Htran'.
  have e : tss = tss1 by firstorder. subst tss1.
  elim: Htran' => [H1' [H2' H3']] {Htran}.
  elim: Hstate2 => a [H4 [H5 [H6 [H7 H8]]]].
  exists a.
  split; [| split; [| split; [| split ]]] => //.
  - elim: (H3' H6); [by elim | by intuition].
  - elim: (H3' H6) => [| [_ [_ H]]]; [by elim | by rewrite H].
  - elim: (H3' H6) => [| [? _]]; [by elim | by []].
pose TR3 := @TR3genacc _ _ Trans Trans' State1 State2
             HreflTrans HtransTrans HreflTrans' HtransTrans'
             Hstep2.
have Harr := Hpure _ _ TR3.
move => a ts res ts1 res1 Hf0 Earg Hf1.
have Hargs : (@IdR _ =R=> StateTR TR3 (@IdR _)) kTest kTest.
  clear - a => {a}.
  move => x x'. elim. rewrite /TR3 /= /TR3gen.
  move => tss tss'.
  case E1 : (kTest x tss) => [xx1 tss1].
  case E1' : (kTest x tss') => [xx1' tss1'].
  split; [| split; [| split; [| split ]]].
  - by exists xx1.
  - by exists xx1'.
  - rewrite /Trans.
    split; [| split].
    + move => H. rewrite /kTest in E1.
      case e : tss.(arg) => [a |] //.
      rewrite e in E1. case: E1 => _ e2. rewrite e2 in e.
      by rewrite e in H.
    + move => [a H]. rewrite /kTest in E1.
      rewrite H in E1. by case: E1.
    + move => H. rewrite /kTest in E1.
      case e : tss.(arg) => [a |].
      * rewrite e in E1. left. by case: E1.
      * rewrite e H in E1. right.
        case: E1 => _ E1. by rewrite -E1 /=; eauto.
  - rewrite /Trans' /Trans.
    split; [| split].
    + move => H. rewrite /kTest in E1'.
      case e : tss'.(arg) => [a |] //.
      rewrite e in E1'. case: E1' => _ e2. rewrite e2 in e.
      by rewrite e in H.
    + move => [a H]. rewrite /kTest in E1'.
      rewrite H in E1'. by case: E1'.
    + move => H. rewrite /kTest in E1'.
      case e : tss'.(arg) => [a |].
      * rewrite e in E1'. left. by case: E1'.
      * rewrite e H in E1'. right.
        case: E1' => _ E1'. by rewrite -E1' /=; eauto.
  - move => Hstate.
    rewrite /State1 in Hstate. elim: Hstate => [e1 [e2 [e3 e4]]].
    rewrite /kTest in E1. rewrite e1 in E1.
    case: (destruct_seq tss.(ans)); last first
      => [Hans | [hb [tb Hans]]].
    + rewrite Hans in E1. rewrite Hans cat0s in e3.
      case: E1 => _ E1.
      rewrite /kTest in E1'. rewrite e2 e3 /= in E1'.
      case: E1' => _ E1'.
      right. rewrite /State2.
      by rewrite -E1 -E1' e4 /=; exists x.
    + rewrite Hans /= in E1.
      case: E1 => e E1. subst hb.
      have e : tb = tss1.(ans) by rewrite -E1. subst tb.
      rewrite /State1.
      rewrite /kTest in E1'. rewrite e2 e3 Hans /= in E1'.
      case: E1' => e' E1'. subst xx1'.
      left. by rewrite -E1 -E1' e4.
have Htmp := Harr _ _ Hargs (initTest bs) (initTest (bs ++ [::b])).
rewrite Hf0 Hf1 in Htmp.
elim: Htmp => [_ [_ [_ [Htran' Himp]]]].
have Hstate1 : State1 (initTest bs) (initTest (bs ++ [:: b]))
  by [].
elim: (Himp Hstate1) => [[[Habs _] _] | Hstate2].
- by rewrite Earg in Habs.
- rewrite /State2 Earg in Hstate2.
  elim: Hstate2 => a0 [E Hstate2].
  inversion_clear E. by intuition.
Qed.


Theorem FunTreeFun_gen
          (F : FuncType A B C) (Hpure : isPure F) S k :
  forall bbs t, Fun2Tree F bbs t -> 
    forall s s' aas c ts, 
      F TestSet kTest (initTest bbs) = (c, ts) ->
      ts.(que) = aas ->
      Matches k aas bbs s s' ->
      let (c1, s1) := F S k s in
      let (c2, s2) := tree2fun t k s' in
          c1 = c2 /\ s1 = s2.
Proof.
move => ds t; move: ds.
elim: t => [c | a f IH].
- move => bbs HfunAns.
  elim: (Fun2Tree_Ans_elim HfunAns) => [r [e1 e2]] {HfunAns}.
  move => s sch aas c0 r0 Hf Hque Hmat.
  rewrite Hf in e1. case: e1 => ? ?; subst c0 r0.
  case E1 : (F S k s) => [c1 s1].
  case E2 : (tree2fun (Ans c) k sch) => [c2 s2].
  rewrite /= /valState /= in E2.
  case: E2 => ? ?; subst c2 s2.
  subst aas.
  by apply: (LemBaseCase _ Hf Hmat).
- move => bbs HfunQue.
  elim: (Fun2Tree_Que_elim HfunQue)
    => [r [c [e1 [e2 H]]]] {HfunQue}.
  move => s sch aas c0 r0 Hf Hque Hmat.
  subst aas.
  rewrite Hf in e1.
  case: e1 => ? ?; subst c0 r0.
  case E1 : (F S k s) => [c1 s1].
  case E2 : (tree2fun (Que a f) k sch) => [c2 s2].
  rewrite /= /bindState /tbind /= in E2.
  case Ek : (k a sch) => [b s2']. rewrite Ek in E2.
  have Hmat2 : Matches k (que r ++ [:: a]) (bbs ++ [:: b]) s s2'
    by apply: MatchesC; eauto.
  case E : (F TestSet kTest (initTest (bbs ++ [:: b])))
    => [c' ts'].
  have Htmp := IH b _ (H b) _ _ _ _ _ E _ Hmat2.
  have Hcase := (LemStepCase Hpure Hf e2) E.
  rewrite E1 E2 in Htmp.
  by apply: Htmp.
Qed.

Lemma que_nil (F : FuncType A B C) (Hpure : isPure F) :
  forall ts v,
    F _ kTest (initTest [::]) = (v, ts) ->
    ts.(que) = nil.
Proof.
pose Trans : relation TestSet :=
  fun ts ts1 =>
    ts.(ans) = nil /\ ts.(que) = nil ->
    ts1.(ans) = nil /\ ts1.(que) = nil.
have HreflTrans : reflexive _ Trans by firstorder.
have HtransTrans : transitive _ Trans by firstorder.
pose Trans' : relation TestSet := fun _ _ => True.
have HreflTrans' : reflexive _ Trans' by [].
have HtransTrans' : transitive _ Trans' by [].
pose TR := @TRtransacc _ _ Trans Trans'
             HreflTrans HtransTrans
             HreflTrans' HtransTrans'.
have Harr := Hpure _ _ TR.
have Hargs : (@IdR _ =R=> StateTR TR (@IdR _)) kTest kTest.
  move => x x'. elim. rewrite /TR /= /TRtrans /=.
  move => ts ts'.
  case E : (kTest x ts) => [x1 ts1].
  case E' : (kTest x ts') => [x1' ts1'].
  split; [| split; [| split; [| split ]]] => //.
  - by exists x1.
  - by exists x1'.
  - rewrite /Trans. rewrite /kTest in E.
    move => [H1 H2].
    case e : ts.(arg) => [a |] //; rewrite e in E.
    + case: E => _ e2. by rewrite -e2.
    + rewrite H1 in E. case: E => _ e2. by rewrite -e2 H2.
have Htmp := Harr _ _ Hargs (initTest [::]) (initTest ([::])).
move => {Harr Hargs}.
move => ts v H. rewrite H in Htmp.
elim: Htmp => [_ [_ [Htmp _]]].
rewrite /Trans in Htmp. by intuition.
Qed.

Theorem FunTreeFun (F : FuncType A B C) (Hpure : isPure F) S k :
  forall t, Fun2Tree F [::] t -> 
    forall s,
      let (c1, s1) := F S k s in 
      let (c2, s2) := tree2fun t k s in
          c1 = c2 /\ s1 = s2.
Proof.
move => t H s.
case E : (F _ kTest (initTest [::])) => [v2 ts].
have Hque : ts.(que) = [::] by apply: (que_nil Hpure E).
have Hmat : Matches k [::] [::] s s by apply: MatchesN.
by apply: FunTreeFun_gen; eauto.
Qed.

(*Fixpoint subtree A B C (t : Tree A B C) (path : seq B) :=
  match t, path with
    | _, nil => t
    | Ans _, _ => t
    | Que x k, b :: bs => subtree (k b) bs
  end.*)

Section Streams.
Variable A : Type.

CoInductive Stream : Type :=
  | Nil : Stream
  | Cons : A -> Stream -> Stream.

Definition Stream_decompose (s : Stream) : Stream :=
  match s with
    | Nil => Nil
    | Cons h t => Cons h t
  end.

Lemma Stream_decompose_lemma s : s = Stream_decompose s.
Proof. by case: s. Qed.

(*Lemma Stream_unfold x :
  x = match x with
        | Nil => Nil
        | Cons a s => Cons a s
      end.
Proof. by case: x. Qed.*)

Lemma not_Nil_Cons s :
  ~ s = Nil -> exists h t, s = Cons h t.
Proof.
case: s => [// |]; by eauto.
Qed.

Fixpoint seqToStream (s : seq A) : Stream :=
  match s with
    | [::] => Nil
    | h :: t => Cons h (seqToStream t)
  end.

Fixpoint firstN n (s : Stream) : seq A :=
  match n with
    | 0 => [::]
    | n.+1 =>
        match s with
          | Nil => [::]
          | Cons h t => h :: firstN n t
        end
  end.

Fixpoint catSeqStream (s1 : seq A) (s2 : Stream) : Stream :=
  match s1 with
    | [::] => s2
    | h :: t => Cons h (catSeqStream t s2)
  end.

Lemma catSeqStream_cat s1 s2 s3 :
  catSeqStream s1 (catSeqStream s2 s3) =
  catSeqStream (s1 ++ s2) s3.
Proof.
elim: s1 => [| h t IH] //=.
by rewrite IH.
Qed.

Lemma catSeqStream_Nil s :
  catSeqStream s Nil = seqToStream s.
Proof.
elim: s => [| h t IH] //=.
by rewrite IH.
Qed.

Lemma catSeqStream_firstN s p r :
  s = catSeqStream p r -> exists n, p = firstN n s.
Proof.
move: s.
elim: p => [| h t IH].
- rewrite /=. by move => s _; exists 0.
- move => s e.
  rewrite /= in e.
  elim: (IH _ Logic.eq_refl) => n Hn.
  exists n.+1.
  by rewrite e [in X in X = _]Hn.
Qed.

(*CoFixpoint catStream (s1 s2 : Stream) : Stream :=
  match s1 with
    | Nil => s2
    | Cons h t => Cons h (catStream t s2)
  end.

Lemma catStream_nil (s : Stream) :
  catSeqStream [::] s = s.
by [].
Qed.

Definition catSeqStream_bis (s1 : seq A) (s2 : Stream)
  := catStream (seqToStream s1) s2.*)

CoFixpoint funToStream_from n (f : nat -> A) : Stream
  := Cons (f n) (funToStream_from n.+1 f).

Definition funToStream f := funToStream_from 0 f.

Inductive Finite : Stream -> Prop :=
  | Nil_fin : Finite Nil
  | Cons_fin : forall a s, Finite s -> Finite (Cons a s).

CoInductive Infinite : Stream -> Prop :=
  | Cons_inf : forall a s, Infinite s -> Infinite (Cons a s).

Lemma seq_Finite s : Finite (seqToStream s).
Proof.
elim: s => [| h t IH] //=; by constructor.
Qed.

Lemma catSeqStream_Finite s1 s2 :
  Finite s2 -> Finite (catSeqStream s1 s2).
Proof.
elim: s1 => [| h t IH] //=.
move => H. by constructor; auto.
Qed.

Lemma Infinite_elim s :
  Infinite s -> exists a t, s = Cons a t /\ Infinite t.
Proof.
case; by eauto.
Qed.

Lemma Infinite_not_Nil s : Infinite s -> ~ s = Nil.
Proof.
move => Hinf.
elim: (Infinite_elim Hinf) => h [t [? _]].
by subst s.
Qed.

Lemma catSeqStream_Infinite_1 l s :
  Infinite s -> Infinite (catSeqStream l s).
Proof.  
elim: l => [| a h IH]; by intuition.
Qed.

Lemma catSeqStream_Infinite_2 l s :
  Infinite (catSeqStream l s) -> Infinite s.
Proof.
elim: l => [| a h IH] //=.
move => H. by inversion H; intuition.
Qed.

Lemma funToStream_from_unfold n f :
  funToStream_from n f = Cons (f n) (funToStream_from n.+1 f).
Proof.
by rewrite [X in X = _] Stream_decompose_lemma.
Qed.

Lemma funToStream_from_Infinite f :
  forall n, Infinite (funToStream_from n f).
Proof.
cofix H.
move => n.
rewrite funToStream_from_unfold.
constructor.
by apply: H.
Qed.

Lemma funToStream_Infinite f : Infinite (funToStream f).
Proof.
by apply: funToStream_from_Infinite.
Qed.

Lemma Nil_not_Infinite : ~ Infinite Nil.
Proof.
move => H. by inversion H.
Qed.
Hint Resolve Nil_not_Infinite.

Lemma Finite_not_Infinite s :
  Finite s -> ~ Infinite s.
Proof.
move => H. elim: H => //.
move => h t Hf Hi Hicons.
case: Hi. by inversion Hicons.
Qed.

Lemma not_Finite_Infinite s :
  ~ Finite s -> Infinite s.
Proof.
move: s. cofix H. case.
- by have Habs : Finite Nil by constructor.
- move => h t Hcons.
  constructor.
  apply: H => H. elim: Hcons. by constructor.
Qed.

End Streams.

Arguments Nil [A] : default implicits.

Record TestISet := mkTestI
  { argI : option A;
    queI : seq A;
    ansI : Stream B }.

Definition initTestI (bs : Stream B) : TestISet :=
  {| argI := None;
     queI := nil;
     ansI := bs |}.

Definition kTestI : A -> State TestISet B := 
  fun a s =>
    match s.(argI) with
      | Some _ => (botB, s)
      | None =>
          match s.(ansI) with
            | Nil =>
                (botB, {| argI := Some a;
                          queI := s.(queI);
                          ansI := Nil |})
            | Cons b bs =>
                (b, {| argI := s.(argI);
                       queI := (s.(queI) ++ [::a]);
                       ansI := bs |})
          end
    end.

Coercion TestToTestI (s : TestSet) : TestISet :=
  {| argI := s.(arg);
     queI := s.(que);
     ansI := seqToStream s.(ans) |}.

Lemma Test_TestI_sim (F : FuncType A B C) (Hpure : isPure F) :
  forall s,
    let (c1,s1) := F _ kTest s in
    let (c1',s1') := F _ kTestI s in
      c1 = c1' /\ (s1 : TestISet) = s1'.
Proof.
pose P : Rel TestSet TestISet
  := fun r ri => (r : TestISet) = ri.
pose TR := TRparamAcc P.
have Harr := Hpure _ _ TR.
have Hargs : (@IdR _ =R=> StateTR TR (@IdR _)) kTest kTestI.
  move => x x'. elim => {x'}.
  rewrite /TR /TRparamAcc /= /TRparam.
  move => r r' Hrr'.
  rewrite /P in Hrr'. subst r'.
  case e: (kTest x r) => [c1 s1].
  case e': (kTestI x r) => [c1' s1'].
  rewrite /kTest in e. rewrite /kTestI in e'.
  have Harg : r.(arg) = r.(argI) by [].
  have Hans : seqToStream r.(ans) = r.(ansI) by [].
  rewrite -Harg in e' => {Harg}.
  case Earg : (arg r) => [a |]; rewrite Earg in e e' => {Earg}.
  - by case: e; elim; elim; case: e'; elim; elim.
  - rewrite -Hans in e'.
    case Eans : r.(ans) => [| a aas]; rewrite Eans /= in e e'.
    + by case: e; elim; elim; case: e'; elim; elim.
    + case: e => ? e; subst c1.
      case: e' => ? e'; subst c1'.
      split => //.
      by rewrite -e -e'.
move => r.
have Hrr : P r r by [].
have Htmp := Harr _ _ Hargs r r Hrr => {Harr Hargs Hrr}.
case e : (F _ kTest r) => [c1 r1].
case e' : (F _ kTestI r) => [c1' r1'].
rewrite e e' in Htmp.
by firstorder.
Qed.

Lemma lem01 (F : FuncType A B C) (Hpure : isPure F) :
  forall bs c r,
    F _ kTestI (initTestI bs) = (c,r) ->
    (exists a, r.(argI) = Some a) ->
    r.(ansI) = Nil.
Proof.
pose Trans : relation TestISet
  := fun r r1 =>
       (r.(argI) = None ->
        (exists a, r1.(argI) = Some a) -> r1.(ansI) = Nil) /\
       (r.(ansI) = Nil -> r1.(ansI) = Nil).
have HreflTrans : reflexive _ Trans.
  move => r. rewrite /Trans. split => //.
  move => H [a Habs]; by rewrite H in Habs.
have HtransTrans : transitive _ Trans.
  rewrite /Trans => r1 r2 r3 H12 H23.
  split; last by intuition.
  move: H12 H23.
  case Earg : (argI r2) => [a |]; by intuition; eauto.
pose Trans' : relation TestISet := fun _ _ => True.
have HreflTrans' : reflexive _ Trans' by [].
have HtransTrans' : transitive _ Trans' by [].
pose Inv : relation TestISet := fun s s' => s = s'.
pose TR := @TR1genacc _ _ Trans Trans' Inv
            HreflTrans HtransTrans HreflTrans' HtransTrans'.
have Harr := Hpure _ _ TR.
have Hargs : (@IdR _ =R=> StateTR TR (@IdR _)) kTestI kTestI.
  move => x x'. elim => {x'}.
  rewrite /TR /= /TR1gen.
  move => s s'.
  case E1 : (kTestI x s) => [x1 s1].
  case E1' : (kTestI x s') => [x1' s1'].
  split; [| split; [| split; [| split ]]] => //.
  - by exists x1.
  - by exists x1'.
  - rewrite /Trans.
    rewrite /kTestI in E1.
    split.
    + move => Harg; rewrite Harg in E1.
      move: E1; case: (ansI s) => [| b bs] /=;
        by case => _ ?; subst s1; firstorder.
    + move => Hans.
      move: E1; case: (argI s) => [a |].
      * by case => _ ?; subst s1.
      * rewrite Hans. by case => _ ?; subst s1.
  - rewrite /Inv /IdR. move => ?; subst s'.
    by rewrite E1 in E1'; case: E1'.
move => bs c s Hf.
have Htmp := Harr _ _ Hargs (initTestI bs) (initTestI bs).
rewrite Hf in Htmp.
by firstorder.
Qed.

(* The following lemma claims that only finitely many answers can
   be used. *)
Lemma lem02 (F : FuncType A B C) (Hpure : isPure F) :
  forall bs c r,
    F _ kTestI (initTestI bs) = (c,r) ->
    exists ans,
      bs = catSeqStream ans r.(ansI) /\
      size r.(queI) = size ans.
Proof.
pose Trans : relation TestISet
  := fun r r1 =>
       (exists bb aa,
          r.(ansI) = catSeqStream bb r1.(ansI) /\
          r1.(queI) = r.(queI) ++ aa /\
          size bb = size aa).
have HreflTrans : reflexive _ Trans.
  move => r. rewrite /Trans.
  by exists [::], [::]; rewrite cats0.
have HtransTrans : transitive _ Trans.
  rewrite /Trans => s1 s2 s3 [ans1 [que1 [H11 [H12 H13]]]]
                             [ans2 [que2 [H21 [H22 H23]]]].
  exists (ans1 ++ ans2), (que1 ++ que2).
  by rewrite H11 H21 H22 H12 catSeqStream_cat catA
     !size_cat H13 H23.
pose Trans' : relation TestISet := fun _ _ => True.
have HreflTrans' : reflexive _ Trans' by [].
have HtransTrans' : transitive _ Trans' by [].
pose Inv : relation TestISet := fun s s' => s = s'.
pose TR := @TR1genacc _ _ Trans Trans' Inv
            HreflTrans HtransTrans HreflTrans' HtransTrans'.
have Harr := Hpure _ _ TR.
have Hargs : (@IdR _ =R=> StateTR TR (@IdR _)) kTestI kTestI.
  move => x x'. elim => {x'}.
  rewrite /TR /= /TR1gen.
  move => s s'.
  case E1 : (kTestI x s) => [x1 s1].
  case E1' : (kTestI x s') => [x1' s1'].
  split; [| split; [| split; [| split ]]] => //.
  - by exists x1.
  - by exists x1'.
  - rewrite /Trans.
    rewrite /kTestI in E1.
    move: E1; case: (argI s) => [a |].
    + case => _ ?; subst s1.
      by exists [::], [::]; rewrite cats0.
    + case: (ansI s) => [| b bs].
      * case => _ ?; subst s1 => /=.
        by exists [::], [::]; rewrite cats0.
      * case => _ ?; subst s1 => /=.
        by exists [::b], [::x].
  - rewrite /Inv /IdR. move => ?; subst s'.
    by rewrite E1 in E1'; case: E1'.
move => bs c r Hf.
have Htmp := Harr _ _ Hargs (initTestI bs) (initTestI bs).
rewrite Hf in Htmp.
elim: Htmp => [_ [_ [H _]]].
clear - H.
rewrite /Trans /= in H.
case: H => [bb [aa H]].
exists bb. 
by firstorder; congruence.
Qed.

Lemma lem03 (F : FuncType A B C) (Hpure : isPure F) bs c r :
  Infinite bs ->
  F _ kTestI (initTestI bs) = (c,r) ->
  r.(argI) = None.
Proof.
move => Hinf Hf.
elim Earg: (argI r) => [a | //].
have Eans: r.(ansI) = Nil by apply: (lem01 _ Hf); eauto.
elim: (lem02 Hpure Hf) => ans [Hans _].
rewrite Eans catSeqStream_Nil in Hans.
have Habs: Finite bs by rewrite Hans; apply: seq_Finite.
by elim: (Finite_not_Infinite Habs).
Qed.

Definition sim r rI bs
  := r.(arg) = rI.(argI) /\
     r.(que) = rI.(queI) /\
     catSeqStream r.(ans) bs = rI.(ansI).

Lemma sim_kTest r rI b bs bsI a (Hne : ~ bsI = Nil) :
  sim r rI bsI ->
  r.(ans) = b :: bs ->
  fst (kTest a r) = fst (kTestI a rI).
Proof.
elim: (not_Nil_Cons Hne) => b' [bsI' H].
move => [e1 [e2 e3]] Eans.
case E1 : (kTest a r) => [b1 r1].
case E1' : (kTestI a rI) => [b1' rI1'].
rewrite /kTest in E1.
rewrite /kTestI in E1'.
case Earg: (arg r) => [a0 |].
- rewrite Earg in E1.
  rewrite -e1 Earg in E1'.
  by case: E1 => ? ?; subst b1 r1;
     case: E1' => ? ?; subst b1' rI1'.
- rewrite Earg Eans in E1.
  rewrite -e1 Earg -e3 Eans /= in E1'.
  by case: E1 => ? ?; subst b1 r1;
     case: E1' => ? ?; subst b1' rI1'.
Qed.

Lemma Infinite_kTestI a r r1 b1 :
  kTestI a r = (b1, r1) ->
  Infinite (r.(ansI)) ->
  Infinite (r1.(ansI)).
Proof.
move => H Hinf.
rewrite /kTestI in H.
case Harg : (r.(argI)) => [a0 |].
- rewrite Harg in H.
  by case: H => _ ?; subst r1.
- rewrite Harg in H => {Harg}.
  elim: (Infinite_elim Hinf) => b [bs [e Hbs]].
  rewrite e in H.
  by case: H => _ ?; subst r1.
Qed.

Lemma lem04 (F : FuncType A B C) (Hpure : isPure F) :
  forall bs bsI c c' r r',
    ~ bsI = Nil ->
    F _ kTest (initTest bs) = (c,r) ->
    F _ kTestI (initTestI (catSeqStream bs bsI)) = (c',r') ->
    r.(arg) = None /\ sim r r' bsI \/
    (exists a, r.(arg) = Some a) /\ size r.(que) < size r'.(queI).
Proof.
move => bs bsI c c' r r' Hne.
pose Trans : relation TestSet := fun r r1 =>
  (exists a, r.(arg) = Some a) -> r = r1.
have HreflTrans : reflexive _ Trans.
  move => ts. rewrite /Trans. by intuition.
have HtransTrans : transitive _ Trans.
  move => ts1 ts2 ts3 H12 H23.
  rewrite /Trans. rewrite /Trans in H12, H23.
  move => Hcal1.
  have E12 : ts1 = ts2 by intuition.
  subst ts1; by auto.
pose Trans' : relation TestISet := fun r r1 =>
  size r.(queI) <= size r1.(queI).
have HreflTrans' : reflexive _ Trans'
  by have H := leqnn; firstorder.
have HtransTrans' : transitive _ Trans'
  by have H := leq_trans; firstorder.
pose State1 : TestSet -> TestISet -> Prop
  := fun r r' =>
       r.(arg) = None /\
       sim r r' bsI.
pose State2 : TestSet -> TestISet -> Prop
  := fun r r' =>
       (exists a, r.(arg) = Some a) /\
       r.(ans) = nil /\
       size r.(que) < size r'.(queI).
have Hstep2 : stepTransState2 Trans Trans' State2.
  move => ts ts' ts1 ts1' Hstate2 Htran Htran'.
  rewrite /State2.
  rewrite /State2 in Hstate2.  
  rewrite /Trans in Htran. rewrite /Trans' in Htran'.
  have e : ts = ts1 by firstorder. subst ts1.
  move => {Htran}.
  elim: Hstate2 => H1 [H2 H3].
  split; [| split] => //.
  - idtac. move: Htran' => Hsize1.
    clear - H3 Hsize1.
    move: H3 Hsize1;
      generalize (size (que ts)) (size (queI ts'))
                 (size (queI ts1')).
    move => m p n H H0.
    rewrite -(ltn_add2r 1) !addn1.
    by apply: (@leq_ltn_trans p).
pose TR := @TR3genacc _ _ Trans Trans' State1 State2
             HreflTrans HtransTrans HreflTrans' HtransTrans'
             Hstep2.
have Harr := Hpure _ _ TR.
have Hargs : (@IdR _ =R=> StateTR TR (@IdR _)) kTest kTestI.
  move => x x'. elim => {x'}. rewrite /TR /= /TR3gen.
  move => ts ts'.
  case E1 : (kTest x ts) => [b1 ts1].
  case E1' : (kTestI x ts') => [b1' ts1'].
  split; [| split; [| split; [| split ]]].
  - by exists b1.
  - by exists b1'.
  - rewrite /Trans.
    move => [a H]. rewrite /kTest in E1.
    rewrite H in E1. by case: E1.
  - rewrite /Trans'.
    rewrite /kTestI in E1'.
    case e : ts'.(argI) => [a |].
    + rewrite e in E1'. case: E1' => _ e2. by rewrite e2.
    + rewrite e in E1'.
      move: E1'. case: (ansI ts') => [| b bbs].
      case => _ ?; by subst ts1'.
      case => _ ?; subst ts1' => /=.
      rewrite size_cat /= addn1.
      by apply: leqnSn.
  - move => Hstate.
    rewrite /State1 in Hstate.
    elim: Hstate => [e1 Hsim].
    case: (Hsim) => [e3 [e4 e5]].
    have Hb := sim_kTest x Hne Hsim => {Hsim}.
    rewrite E1 E1' /= in Hb.
    rewrite /kTest in E1. rewrite e1 in E1.
    case Hans : (ts.(ans)) => [| hb tb].
    + right.
      rewrite Hans in E1. rewrite Hans /= in e5.
      case: E1 => _ E1.
      rewrite /kTestI in E1'. rewrite -e3 e1 -e5 /= in E1'.
      elim: (not_Nil_Cons Hne) => h [t e].
      rewrite e in E1'.
      case: E1' => _ ?; subst ts1'.
      rewrite /State2 /=.
      by rewrite -E1 -e4 size_cat addn1 /=; eauto.
    + left.
      rewrite Hans /= in E1.
      have eb : b1 = b1' by apply: Hb; eauto.
      subst b1' => {Hb}. split => //.
      case: E1 => ? E1; subst hb.
      have e : tb = ts1.(ans) by rewrite -E1. subst tb.
      rewrite /State1.
      rewrite /kTestI in E1'.
      elim: (not_Nil_Cons Hne) => hb [tb EansI].
      rewrite -e3 e1 -e5 Hans /= in E1'.
      case: E1' => ?; subst ts1'.
      by rewrite -E1 /sim -e4 /=.
move => Hf Hf'.
have Htmp := Harr _ _ Hargs
                  (initTest bs)
                  (initTestI (catSeqStream bs bsI)).
rewrite Hf Hf' in Htmp.
have Hst1 : State1 (initTest bs) (initTestI (catSeqStream bs bsI))
  by [].
case: Htmp => [_ [_ [_ [_ Himp]]]].
have Htmp := Himp Hst1 => {Himp Hst1}.
clear - Htmp.
rewrite /State1 /State2 in Htmp; by intuition.
Qed.

(* The following hypothesis can be proven classically
   with Axiom of Choice *)
Hypothesis tree_not_exists_cex :
  forall (F : FuncType A B C) (Hpure : isPure F),
    ~ (exists t, Fun2Tree F [::] t) ->
    exists (d : Stream B),
      Infinite d /\
      forall n c s,
        F _ kTest (initTest (firstN n d)) = (c,s) ->
        (exists a, s.(arg) = Some a).

Require Import Classical.

Theorem tree_exists (F : FuncType A B C) (Hpure : isPure F) :
  exists t, Fun2Tree F [::] t.
Proof.
case: (classic (exists t, Fun2Tree F [::] t)) => [// | Habs].
elim: (tree_not_exists_cex Hpure Habs) => bs [Hinf Hbs] {Habs}.
elim E' : (F _ kTestI (initTestI bs)) => [c' r'].
elim: (lem02 Hpure E') => ans [Hans Hsize'].
have Hinf' : Infinite (ansI r')
  by apply: (@catSeqStream_Infinite_2 _ ans); rewrite -Hans.
have Harg' := lem03 Hpure Hinf E'.
elim E : (F _ kTest (initTest ans)) => [c r].
rewrite Hans in E'.
have Htmp := lem04 Hpure (Infinite_not_Nil Hinf') E E'.
case: Htmp => [[Harg Hsim] | [Harg Hltn]].
- elim: (catSeqStream_firstN Hans) => n Hn.
  have Harg1 : exists a, r.(arg) = Some a
    by rewrite Hn in E; apply: (Hbs _ _ _ E).
  by elim: Harg1; congruence.
- have Hans1 := lem_Test_cal_ans Hpure E Harg.
  have Hsize := lem_Test_ans_que Hpure E.
  rewrite Hans1 in Hsize => {Hans1}.
  setoid_rewrite cats0 in Hsize.
  elim: Hsize => bbs [? Hsize]; subst bbs.
  by rewrite Hsize Hsize' ltnn in Hltn.
Qed.
