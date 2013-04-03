(****************************************************************)
(*  On monadic parametricity of second-order functionals        *)
(*  by Bauer A., Hofmann M., Karbyshev A.                       *)
(*                                                              *)
(*  Aleksandr Karbyshev                                         *)
(*  May 2012                                                    *)
(*  Build with Coq 8.4 + Ssreflect 1.4                          *)
(****************************************************************)

Require Import ssreflect ssrbool ssrfun ssrnat.
Set Automatic Coercions Import.
Require Import monads.
Require Import purity.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import List.
Import ListNotations.

Section deps.
Variables A B C : Set.

Definition instr (T : monadType) (f : A -> T B)
  : A -> (StateT (list (A * B)) T) B
  := fun a l =>
       tbind (f a) (fun b => tval _ (b, (l ++ [(a,b)]))).

Fixpoint deps (t : Tree A B C) (f : A -> B) : list (A * B) :=
  match t with
    | Ans _ => nil
    | Que x k => let d := f x in (x, d) :: deps (k d) f
  end.

Definition deps_1 (t : Tree A B C) (f : A -> B) : list (A * B) :=
  let f' : A -> State (list (A * B)) B := @instr Id f in
    snd (tree2fun t f' []).

Lemma deps_1_app (t : Tree A B C) (f : A -> B)
                 (l : list (A * B)) :
  let f' : A -> State (list (A * B)) B := @instr Id f in
    snd (tree2fun t f' l) = l ++ snd (tree2fun t f' []).
Proof.
move => f'.
move: l.
elim: t => [c | a k IHt].
- move => l /=. now rewrite app_nil_r.
- move => l /=.
  rewrite IHt. rewrite <- app_assoc. now rewrite <- IHt.
Qed.

Lemma deps_are_same t f : deps t f = deps_1 t f.
Proof.
elim: t => [c | a k IHt].
- now rewrite /deps_1.
- now rewrite /= /deps_1 /= deps_1_app /= IHt.
Qed.
End deps.

Fixpoint max_seq_aux s accu :=
  match s with
    | [] => accu
    | x :: xs => max_seq_aux xs (maxn x accu)
  end.

Definition max_seq s := max_seq_aux s 0.

Lemma max_seq_aux_leq x s accu :
  x <= accu -> x <= max_seq_aux s accu.
Proof.
move: accu.
elim: s => [// | a s IH /= accu Hx].
apply: IH.
rewrite leq_max; now intuition.
Qed.

Lemma max_seq_aux_leq_accu s accu1 accu2 :
  accu1 <= accu2 -> max_seq_aux s accu1 <= max_seq_aux s accu2.
Proof.
move: accu1 accu2.
elim: s => [// | a s IH accu1 accu2 H /=].
apply: IH.
rewrite geq_max.
apply/andP.
split; [now apply: leq_maxl |
        apply: (leq_trans H); now apply: leq_maxr].
Qed.

Lemma max_seq_spec s :
  forall x, In x s -> x <= max_seq s.
Proof.
rewrite /max_seq.
elim: s => [// | a s IH].
move => x Hx.
case (in_inv Hx) as [e | H].
- rewrite e {e} //=. idtac.
  apply: max_seq_aux_leq. now apply: leq_maxl.
- apply: (leq_trans (IH _ H)).
  now apply: max_seq_aux_leq_accu.
Qed.

(*Fixpoint subtree A B C (t : Tree A B C) (path : list (A * B)) :=
  match t, path with
    | _, nil => Some t
    | Ans _, _ :: _ => None
    | Que x k, (_, b) :: ps => subtree (k b) ps
  end.*)

Fixpoint subtree A B C (t : Tree A B C) (path : list (A * B)) :=
  match t, path with
    | _, nil => t
    | Que x k, (_, b) :: ps => subtree (k b) ps
    | _, _ => t
  end.

Lemma deps_subtree A B C (t : Tree A B C) sigma :
  let c := evaltree t sigma in
  subtree t (deps t sigma) = @Ans A B C c.
Proof.
elim: t => [// | x k H].
move => c. now firstorder.
Qed.
Hint Resolve deps_subtree.

Lemma deps_compat A B C (t : Tree A B C) l f1 f2 :
  l = deps t f1 ->
  (forall p : A * B, (In p l) -> f1 (fst p) = f2 (fst p)) ->
  deps t f1 = deps t f2.
Proof.
move: l.
induction t as [| a k IH ]; auto.
- intros l H H0. subst l. rewrite /=.
  have e : f1 a = f2 a
    by apply: (H0 (a, f1 a)); firstorder.
  rewrite -e {e}.
  f_equal. eapply IH; eauto. now firstorder.
Qed.

Lemma deps_val_compat A B C (t : Tree A B C) l f1 f2 :
  l = deps t f1 ->
  (forall p, In p l -> f1 (fst p) = f2 (fst p)) ->
  evaltree t f1 = evaltree t f2.
Proof.
move => E H.
have Hdeps : deps t f1 = deps t f2
  by (eapply deps_compat; eauto).
have Hf1 := deps_subtree t f1; rewrite /= in Hf1.
have Hf2 := deps_subtree t f2; rewrite /= in Hf2.
rewrite -Hdeps Hf1 in Hf2.
now inversion Hf2.
Qed.

Definition modulus A B C (F : FuncType A B C) f : list (A * B)
  := let f' : A -> State (list (A * B)) B
         := @instr _ _ Id f in
       snd (F _ f' []).

Lemma modulus_corr A B C
        (F : FuncType A B C) (Hpure : is_pure F) f1 f2 m :
  m = modulus F f1 ->
  (forall p, In p m -> f1 (fst p) = f2 (fst p)) ->
  F Id f1 = F Id f2.
Proof.
move => Hm H.
pose t := proj1_sig Hpure.
have Ht : F = tree2fun t by (apply: proj2_sig Hpure).
rewrite !Ht.
rewrite /modulus Ht in Hm.
rewrite -/(deps_1 t f1) -deps_are_same in Hm.
now apply: (@deps_val_compat _ _ _ _ m).
Qed.

Definition modulus_max B C (F : FuncType nat B C) f : nat
  := let args := fst (split (modulus F f)) in max_seq args.

Lemma modulus_max_corr B C
        (F : FuncType nat B C) (Hpure : is_pure F) f1 f2 m :
  m = modulus_max F f1 ->
  (forall i, i <= m -> f1 i = f2 i) ->
  F Id f1 = F Id f2.
Proof.
move => Hm H.
rewrite /modulus_max in Hm.
apply: modulus_corr => //.
move => p Hp /=.
apply: H.
rewrite Hm.
apply: max_seq_spec.
now apply: in_split_l.
Qed.

Definition instr' B n (f : nat -> B) : nat -> Maybe B
  := fun x => if x <= n then Some (f x) else None.

Inductive modulus_option B C (F : FuncType nat B C) f : nat -> nat -> Prop :=
| Modulus_None :
    forall n m,
      F _ (instr' n f) = None -> modulus_option F f (n.+1) m -> modulus_option F f n m
| Modulus_Some :
    forall n b, F _ (instr' n f) = Some b -> modulus_option F f n n.

Lemma modulus_option_function B C (F : FuncType nat B C) f n m1 m2 :
  modulus_option F f n m1 -> modulus_option F f n m2 -> m1 = m2.
Proof.
elim.
- move => {n m1} n m1 Hf H1 H2 H3.
  inversion H3; subst; clear H3; try rewrite H in Hf; by auto.
- move => {n m1} n b Hf H2.
  inversion H2; subst; clear H2; try rewrite H in Hf; by auto.
Qed.

Lemma modulus_option_spec1 B C (F : FuncType nat B C) f n m :
  modulus_option F f n m -> n <= m.
Proof.
elim => //.
- move => {n m} n m Hf H Hle. by apply: ltnW.
Qed.

Lemma modulus_option_spec2 B C f n m a k :
  modulus_option (tree2fun (@Que nat B C a k)) f n m -> a <= m.
Proof.
elim => //=.
move => {n m} n b.
case E: (instr' n f a) => [x |] => //=.
move => _; rewrite /instr' in E.
move: E; by case: (a <= n).
Qed.

Lemma modulus_option_spec3 B C t f n m :
  modulus_option (@tree2fun nat B C t) f n m ->
  forall p, In p (deps t f) -> fst p <= m.
Proof.
move: n m.
elim: t => [c | a k IH].
- by [].
- move => n m /= H [a' b] [e | i].
  + case: e => ? ?; subst.
    rewrite /=. by apply: modulus_option_spec2; eauto.
  + apply: (IH); last by refine i.
    move => {i a' b}.
    elim: H; eauto.
    move => {n m} n m /=.
    case E: (instr' n f a) => [x |] => //=.
    rewrite /instr' in E.
    have le : a <= n by move: E; case: (a <= n).
    rewrite le in E.
    inversion E; clear dependent x.
    move => H.
    by refine (Modulus_Some H).
Qed.

Lemma modulus_option_corr B C (F : FuncType nat B C) (Hpure : is_pure F) f g m :
  modulus_option F f 0 m ->
  (forall i, i <= m -> f i = g i) ->
  F Id f = F Id g.
Proof.
move => Hm H.
pose t := proj1_sig Hpure.
have Ht : F = tree2fun t by (apply: proj2_sig Hpure).
rewrite !Ht.
rewrite Ht in Hm.
apply: (deps_val_compat eq_refl).
move => [a b] i.
apply: H.
by apply: modulus_option_spec3; eauto.
Qed.
