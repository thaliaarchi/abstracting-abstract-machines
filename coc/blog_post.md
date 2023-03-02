# Dependent Types: The Calculus of Constructions

Dependently typed languages are those where terms and types can bind terms and
types—the most powerful of the systems in the lambda cube. Types themselves are
terms with a type, so there is a less clear separation between terms and types.

Coq is the most popular dependently typed programming language, along with Agda
and Idris. These languages feature very strong guarantees about the programs
written in them.

The type theory behind Coq is the calculus of constructions, based on
constructive logic. That is, a proof of existence must supply a witness of some
value satisfying that. This enables powerful interactions between proofs and
programs, because every proof can construct a program.

Coq takes advantage of the observation that computer programs and mathematical
proofs are equivalent, the Curry–Howard correspondence, to convert in both
directions: A proof of a proposition in Coq is constructed by building up a tree
of concrete evidence, which can be thought of as a data structure. An proof of
an implication, A → B, is an evidence transformer from evidence for A to
evidence for B, i.e., a program that manipulates evidence. In converse,
functions can carry proofs as values and produce proofs.

An extension to the Curry–Howard correspondence is the Curry–Howard–Lambek
correspondence, a three-way isomorphism between proofs, programs, and category
theory (morphisms). Coq supports equational equality, as opposed to the usual
structural equality, with [morphisms](https://coq.inria.fr/refman/addendum/generalized-rewriting.html),
which I assume is due to this correspondence, though I have found no citations
for that.

## Resources

I will be following [“A Tutorial Implementation of a Dependently Typed Lambda
Calculus”](https://www.andres-loeh.de/LambdaPi/) (our paper for discussion) for
my implementation. It presents the semantics using abstract definitions.
Alternatively, a similar tutorial, but demonstrated in Racket, is [“Checking
Dependent Types with Normalization by Evaluation: A Tutorial”](https://davidchristiansen.dk/tutorials/nbe/).

The original paper, upon which Coq was built is [“The Calculus of
Constructions”](https://courses.engr.illinois.edu/cs522/sp2016/TheCalculusOfConstructions.pdf)
(Coquand and Huet 1988).

If you've taken the Software Foundations course, you may find the [ProofObjects](https://softwarefoundations.cis.upenn.edu/lf-current/ProofObjects.html)
chapter on the Curry–Howard correspondence helpful.
