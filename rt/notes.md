# Refinement types for ML

> Two examples of subtypes which cannot be specified as refinement types in our
> system are lists without repeated elements (to efficiently represent sets),
> and closed terms in a A-calculus. Intuitively, this is because these sets
> cannot be described by regular expressions. In fact, our rect type
> declarations (with the proper restrictions, see Section 3) have a close
> connection to regular expressions since our declarations specify so-called
> regular tree sets for which many well-understood algorithms exist. Regular
> tree sets have also shown themselves to be useful in the context of typed
> logic programming.

## Topic 1

The express refinement types with regular trees (i.e., the expressivity of
regular expressions). Could refinement types potentially be written with
push-down automata or Turing machines? It would probably be undecidable, though.

Resolution: The benefit of using a regular language is the algorithms available
to analyze it. If a non-regular language were used, then it wouldn't be
decidable. Refinement-typed systems have no runtime overhead over equivalent
systems without refinement types, but a non-regular language may incur
additional residualization.

## Topic 2

Refinement types in the paper focus on predicates over data. What about over
codata or control flow?

Resolution: You could express predicates over control flow, such as the
algorithmic complexity, as over data. The problem is then how to ensure those
additional variables are not residualized. The cost monad is one solution for
this.
