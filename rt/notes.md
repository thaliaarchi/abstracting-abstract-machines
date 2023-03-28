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
push-down automata or Turing machines? It would probably be unsound, though.
