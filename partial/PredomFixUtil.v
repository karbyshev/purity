(****************************************************************)
(*  On monadic parametricity of second-order functionals        *)
(*  by Bauer A., Hofmann M., Karbyshev A.                       *)
(*                                                              *)
(*  Aleksandr Karbyshev                                         *)
(*  May 2012                                                    *)
(*  Build with Coq 8.4 + Ssreflect 1.4                          *)
(****************************************************************)

Set Automatic Coercions Import.
Require Import PredomCore.
Require Import PredomLift.
Require Import PredomFix.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Unset Automatic Introduction.

(* Prove that FIXP operator is a lub of iteration function *)

Section FixpointIter.

Variable D : cppoType.

Definition iter_n (n : natO) : (D =-> D) -> D
  := fun (f : cpoCatType D D) => iter f n.

Lemma iter_n_simpl n f : iter_n n f = iter f n.
Proof.
by [].
Qed.

Lemma iter_n_mon n : monotonic (iter_n n).
Proof.
move => n. move => f g H. by apply: iter_mon.
Qed.

Definition Iter_n n : ordCatType (D -=> D) D := Eval hnf in mk_fmono (iter_n_mon n).

Lemma Iter_n_simpl n f : Iter_n n f = iter f n.
Proof.
by [].
Qed.

Definition Iter_n_cont n : continuous (Iter_n n).
move => n. move => c. rewrite Iter_n_simpl.
apply (Ole_trans (iter_continuous c n)). simpl.
by apply: lub_mon.
Qed.

Definition ITER_n n : (D -=> D) =-> D := Eval hnf in mk_fcont (Iter_n_cont n).

Lemma ITER_n_simpl n f : ITER_n n f = iter f n.
Proof.
by [].
Qed.

Lemma ITER_n_mon : monotonic (ITER_n).
Proof.
move => n m H f. by apply: iter_m.
Qed.

Definition ITER : ordCatType natO ((D -=> D) -=> D) := Eval hnf in mk_fmono (ITER_n_mon).

Lemma ITER_simpl n f : ITER n f = iter f n.
Proof.
by [].
Qed.

Lemma FIXP_lub_ITER : FIXP =-= lub ITER.
Proof.
apply: fmon_eq_intro => f. simpl. apply: lub_eq_compat. by apply: fmon_eq_intro => n.
Qed.

End FixpointIter.

