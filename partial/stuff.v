(****************************************************************)
(*  On monadic parametricity of second-order functionals        *)
(*  by Bauer A., Hofmann M., Karbyshev A.                       *)
(*                                                              *)
(*  Aleksandr Karbyshev                                         *)
(*  May 2012                                                    *)
(*  Build with Coq 8.4 + Ssreflect 1.4                          *)
(****************************************************************)

Set Automatic Coercions Import.
Require Import PredomAll.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition Comp2 D0 D1 D2 D3
  (F : D1 =-> D2 -=> D3) (g : D0 =-> D1) (h : D0 =-> D2) : D0 =-> D3
  := CCOMP _ _ _ (uncurry F, <| g, h |>).

Lemma Comp2_simpl : forall (D0 D1 D2 D3 : cpoType) F g h x,
  @Comp2 D0 D1 D2 D3 F g h x =-= F (g x) (h x).
by [].
Qed.

Lemma uncurry_simpl D0 D1 D2 (f : cpoCatType _ _) x y :
  @uncurry _ D0 D1 D2 f (x, y) = f x y.
by [].
Qed.

Lemma uncurry_mono (D0 D1 D2 : cpoType) : monotonic (@uncurry _ D0 D1 D2).
rewrite /monotonic. move => f g le x. by apply: le.
Qed.

Definition Uncurry D0 D1 D2 := Eval hnf in mk_fmono (@uncurry_mono D0 D1 D2).

Lemma Uncurry_simpl D0 D1 D2 (f : D0 =-> D1 -=> D2) : Uncurry _ _ _ f = uncurry f.
by [].
Qed.

Lemma Uncurry_cont D0 D1 D2 : continuous (@Uncurry D0 D1 D2).
move => c d0. by apply: lub_le_compat.
Qed.

Definition UNCURRY1 D0 D1 D2 : (D0 -=> D1 -=> D2) =-> (D0 * D1 -=> D2)
  := Eval hnf in mk_fcont (@Uncurry_cont D0 D1 D2).

(*Implicit Arguments UNCURRY [D0 D1 D2].*)

Lemma UNCURRY1_simpl D0 D1 D2 (f : D0 =-> D1 -=> D2) :
  UNCURRY1 _ _ _ f = Uncurry _ _ _ f.
by [].
Qed.

(* The operator CURRY is standard *)
Lemma CURRY_simpl D0 D1 D2 (f : cpoCatType _ _) x y :
  @CURRY D0 D1 D2 f x y = f (x, y).
by [].
Qed.

Lemma CURRY_mono (D0 D1 D2 : cpoType) : monotonic (@CURRY D0 D1 D2).
rewrite /monotonic. move => f g le x y. by apply: le.
Qed.

Definition Curry1 D0 D1 D2 := Eval hnf in mk_fmono (@CURRY_mono D0 D1 D2).

Lemma Curry1_simpl D0 D1 D2 (f : D0 * D1 =-> D2) : Curry1 _ _ _ f = CURRY f.
by [].
Qed.

Lemma Curry1_cont D0 D1 D2 : continuous (@Curry1 D0 D1 D2).
move => c d0 d1. by apply: lub_le_compat.
Qed.

Definition CURRY1 D0 D1 D2 : (D0 * D1 -=> D2) =-> (D0 -=> D1 -=> D2)
  := Eval hnf in mk_fcont (@Curry1_cont D0 D1 D2).

(*Implicit Arguments CURRY1 [D0 D1 D2].*)

Lemma CURRY1_simpl D0 D1 D2 (f : D0 * D1 =-> D2) :
  CURRY1 _ _ _ f = Curry1 _ _ _ f.
by [].
Qed.

Definition UNCURRY1_bis (D0 D1 D2 : cpoType) : (D0 -=> D1 -=> D2) =-> D0 * D1 -=> D2
  := CURRY (EV _ _ << <| EV _ _ << <| FST _ _, FST _ _ << SND _ _ |>, SND _ _ << SND _ _ |>).

Lemma UNCURRY1_bis_simpl X Y Z (f : X =-> Y -=> Z) p :
  UNCURRY1_bis _ _ _ f p = uncurry f p.
by [].
Qed.

Definition CURRY1_bis (D0 D1 D2 : cpoType) : (D0 * D1 -=> D2) =-> D0 -=> D1 -=> D2
  := CURRY (CURRY (EV _ _ << <| FST _ _ << FST _ _, <| SND _ _ << FST _ _, SND _ _ |> |>)).

Lemma CURRY1_bis_simpl X Y Z (f : X * Y =-> Z) x y :
  CURRY1_bis _ _ _ f x y = f (x, y).
by [].
Qed.

Definition PROD1_bis (D0 D1 D2 : cpoType) : (D0 -=> D1) * (D0 -=> D2) =-> (D0 -=> D1 * D2)
  := CURRY (<| EV _ _ << <| FST _ _ << FST _ _, SND _ _ |>, EV _ _ << <| SND _ _ << FST _ _, SND _ _ |> |>).

Lemma PROD1_bis_simpl X Y Z (f : X =-> Y) (g : X =-> Z) x :
  PROD1_bis _ _ _ (f, g) x = (f x, g x).
by [].
Qed.

Definition COMP2_bis (D0 D1 D2 D3 : cpoType) : (D1 -=> D2 -=> D3) =-> (D0 -=> D1) -=> (D0 -=> D2) -=> (D0 -=> D3)
  := CURRY (CURRY (CCOMP _ _ _ << <| UNCURRY1 _ _ _ << FST _ _ << FST _ _, PROD1_bis _ _ _ << <| SND _ _ << FST _ _, SND _ _ |> |>)).

Lemma COMP2_bis_simpl D X Y Z (f : X =-> Y -=> Z) (g : D =-> X) (h : D =-> Y) d :
  COMP2_bis _ _ _ _ f g h d = f (g d) (h d).
by [].
Qed.

Definition FCONT_app (D0 D1 D2 : cpoType) : D1 * (D0 -=> D1 -=> D2) =-> (D0 -=> D2)
  := CURRY (EV _ _ << <| EV _ _ << <| SND _ _ << FST _ _, SND _ _ |>, FST _ _ << FST _ _ |>).
