# Higher-Order Functional Reactive Programming without Spacetime Leaks

## Introduction

Synchronous dataflow languages represent programs as fixed networks of
stream-processing nodes that communicate with each other, each node consuming
and producing a statically known number of primitive values at each clock tick.
This delivers strong guarantees on space and time usage.

Functional reactive programming also works with time-varying values (rather than
mutable state) as a primitive abstraction, but signals are first-class values,
and can be used freely, including in higher-order functions and signal-valued
signals, which permits writing programs which dynamically grow and alter the
dataflow network. Problems: Does not enforce causality; Easy to write space
leaks containing all of a signal's history.

Earlier approaches give up on treating signals as first-class values and offer a
collection of combinators to construct stream transformer functions (of type S A
-> S B) from smaller ones. Streams of streams and other time-dependent values
are forbidden. To enable dynamic dataflow graph modification again, additional
ad hoc combinators make unwanted memory leaks possible.

Question: Besides streams of streams, what are other time-dependent values? Is
there a generalization of time dependency to a more general dependently typed
language?

It's possible to use the formulas of linear temporal logic as types for reactive
programs.

### Contributions

- The rule out space and time leaks by construction.
- Instead of using temporal logic formulas as types, they introduce a delay
  modality to simply typed lambda calculus.
- Each expression scheduled for execution on the current time step is forced to
  be evaluated. All old values are deleted. This makes it impossible to obtain a
  reference to a value past its lifetime, preventing space leaks.
- Uses linear types to prevent space leaks and introduces a type-based right to
  allocate memory, without needing to enumerate the exact amount used.

Question: They prove, via a step-indexed Kripke logical relation, that a
well-typed program will not dereference a deleted value. Can this be considered
a generalization of Rust's lifetime model, which is statically checked by the
compiler?

Question: Is it guaranteed that old values are deleted at the earliest-possible
time?
