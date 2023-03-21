# Type directed compilation of row-typed algebraic effects

Algebraic effects subsume specialized control flow concepts, such as exceptions,
state, iterators, and async-await.

What are row types?

What are free monads?

A `handler` in Koka is an instance of an operation interface, with `return` and
`raise` defined. It resembles monad instances with `bind` and `return`.

## Topic 1

How would effect types interact with laziness? If values cannot have effects,
then lazy evaluation could not produce exceptions.

> A key observation on Moggi’s early work on monads was that values and
> computations should be assigned a different type. Koka applies that principle
> where effect types only occur on function types; and any other type, like
> `int`, truly designates an evaluated value that cannot have any effect.

It states it in the context of Koka, but assume it in a wider sense.

## Topic 2

How do algebraic effects compare to typeclasses? Algebraic effects seem like
typeclasses with dynamic, lexically-scoped instance resolution.
