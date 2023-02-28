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
