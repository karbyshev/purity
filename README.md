Purity
======

The repository contains a formal Coq development accompanying the paper
"On Monadic Parametricity of Second-Order Functionals"
by Andrej Bauer, Martin Hofmann and Aleksandr Karbyshev
(to appear in FoSSaCS 2013).

## Abstract
How can one rigorously specify that a given ML functional
`f : (int -> int) -> int`
is *pure*, i.e., `f` produces no computational effects except those
produced by evaluation of its functional argument?
In this paper, we introduce a semantic notion of *monadic parametricity*
for second-order functionals which is a form of purity.
We show that every monadically parametric `f` admits a question-answer
strategy tree representation.
We discuss possible applications of this notion, e.g., to the
verification of generic fixpoint algorithms.
The results are presented in two settings: a total set-theoretic
setting and a partial domain-theoretic one.
All proofs are formalized by means of the proof assistant Coq.
