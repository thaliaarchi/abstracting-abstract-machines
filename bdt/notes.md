# Bidirectional Typing

> Bidirectional typing combines two modes of typing: type checking, which checks
> that a program satisfies a known type, and type synthesis, which determines a
> type from the program. Using checking enables bidirectional typing to support
> features for which inference is undecidable; using synthesis enables
> bidirectional typing to avoid the large annotation burden of explicitly typed
> languages. In addition, bidirectional typing improves error locality.

Γ ⊢ e : A
- type checking: Γ, e, and A are inputs
- type inference: A is an output
- typing inference: only e is an input
- program synthesis: e is an output

(Γ is the typing context, e is the term, A is the type)

## Discussion

### Topic 1

What is the purpose of the *Anno* rule? If the type of *e* is already known, why
is it useful to annotate it? Does this refer to user-specified type annotations?
I would think, if so, that the annotation would instead be a premise.

   Γ ⊢ e : A
--------------- Anno
Γ ⊢ (e : A) : A

Resolution: If you can judge *e* as type *A*, then you can judge *e*,
syntactically annotated with *A*, as type *A*.

### Topic 2

What is typing inference? It is defined an inference, for when when only *e* is
an input in Γ ⊢ e : A, that is, *Γ* and *A* are inferred as outputs. Why would
inferring the typing context be useful? It is only mentioned as an aside and I
can't find further details.

Resolution: Typing inference would be useful for incremental type inference.
Instead of inferring types top-down and assembling the context, typing inference
could infer types bottom-up, incrementally unifying the contexts, which allows
for types of identical expressions to be reused across compilations.

If it is simply a reversal of direction of regular type inference, then it would
seem to infer the same types as regular type inference. I wonder how it would
interact with type checking. Would rules similar to those in bidirectional
typing hold?

I figure the bottom-up nature would interact well with local transformations
that require inferred type information, because it would allow those to also be
incremental.

Further reading: I should read “What are principal typing and what are they good
for?” (Jim 1995) and “The essence of principal typings” (Wells 2002), which this
paper cites for typing inference.
