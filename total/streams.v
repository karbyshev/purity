Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import Utf8.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Streams.
Variable A : Type.

CoInductive Stream :=
  | Nil : Stream
  | Cons : A -> Stream -> Stream.

Definition Stream_decompose (s : Stream) : Stream :=
  match s with
    | Nil => Nil
    | Cons h t => Cons h t
  end.

Lemma Stream_decompose_lemma s : s = Stream_decompose s.
Proof.
by case: s.
Qed.

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