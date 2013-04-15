Purity
======

The repository contains a formal Coq development accompanying the papers

1. Andrej Bauer, Martin Hofmann and Aleksandr Karbyshev.
   On Monadic Parametricity of Second-Order Functionals, FoSSaCS 2013.
2. Martin Hofmann, Aleksandr Karbyshev, and Helmut Seidl.
   What is a pure functional?, ICALP 2010.

## Abstract
How can one rigorously specify that a given ML functional
`f : (int -> int) -> int` is *pure*, i.e., `f` produces no computational
effects except those produced by evaluation of its functional argument?
In this paper, we introduce a semantic notion of *monadic parametricity*
for second-order functionals which is a form of purity.
We show that every monadically parametric `f` admits a question-answer
strategy tree representation.
We discuss possible applications of this notion, e.g., to the
verification of generic fixpoint algorithms.
The results are presented in two settings: a total set-theoretic setting
and a partial domain-theoretic one.
All proofs are formalized by means of the proof assistant Coq.

## The total case
* firstorder.v
  - Trivial case of purity for the first-order
* icalpN.v
  - General case of second-order functionals parametric in state monads (ICALP '10)
* icalp.v
  - Parametricity in state monads (ICALP '10)
* modulus.v
  - Modulus of continuity
* monads.v
  - Monads
* purityN.v
  - General case of monadic parametricity for the second-order
* purityTree.v
  - Proof of main result using Tree monad
* purity.v
  - Monadic parametricity
* relations.v
  - Relations and monadic liftings
* streams.v
  - Streams
* typeddensem.v
  - Monadic semantics for simply-typed lambda calculus
* typedparam.v
  - Parametricity theorem

## The partial case
* Categories.v
* NSetoid.v
* PredomAll.v
* PredomCore.v
* PredomFixUtil.v
  - Extra facts about fixpoint operator
* PredomFix.v
* PredomKleisli.v
* PredomLiftClassical.v
  - Proof (uses Excluded Middle) that every element in a constructive lifted domain
    is either bottom or a value
* PredomLift.v
* PredomRec.v
* PredomSum.v
* firstorder.v
  - Trivial case of purity for the first-order
* monads.v
  - Monads
* purity.v
  - Monadic parametricity
* relations.v
  - Relations and monadic liftings
* strategy.v
  - Domain of strategies
* stuff.v
* typeddensem.v
  - Monadic semantics for simply-typed lambda calculus
* typedparam.v
  - Parametricity theorem
