# Galois Transformers and Modular Abstract Interpreters

## Topic 1

How does an abstract interpreter handle control flow merges? As I understand it,
abstract time increments for every step. Then if the CFG merges, wouldn't every
branch have the same time? Then the abstract values would be merged, and it
would be less accurate.

## Topic 2

Could this be combined with Collapsing Towers of Interpreters, to provide one
specification, that can be instantiated as an interpreter, abstract interpreter,
or compiler? The semantics of λ⇅ can be changed by using a modified evaluator,
so would that be sufficient to make values abstract?
