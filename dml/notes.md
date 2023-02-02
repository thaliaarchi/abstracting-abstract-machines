# Dependent Types in Practical Programming

Presents an enriched ML type system with a restricted form of dependent types,
where type index objects are drawn from a constraint domain C.

An example with dependent types:

> Suppose that we intend to specify that an implementation of the evaluation
> function for the pure call-by-value λ-calculus returns a closure (if it
> terminates) when given a closed λ-expression. It seems difficult in ML, if not
> impossible, to construct a type for closed lambda expressions. With dependent
> types, this can be done elegantly.

Dependent ML design choices:
- Effects: To avoid effectful operations in indices, index objects must be pure.
- Decidability and practicality: DML(C) is elaborated, preserving operational
  semantics, to a verbose, explicitly typed language, for which type checking is
  easily reduced to constraint satisfaction in C.
- Interfacing: Existential dependent types are used to interface between
  dependently annotated and other parts of a program.
