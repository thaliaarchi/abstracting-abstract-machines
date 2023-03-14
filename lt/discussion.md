# Discussion

## 2023-03-14

What if you could specify a type system to use as an effect handler for a region
of code? This seems like it would interact with co-data and resemble monads.

Perhaps the base language would be a full structural type system, then you could
specify that you want contraction disabled for a region and you have affine
types.

It would allow for domain-specific type systems.

Dependent types seem to be on a separate axis from substructural type systems,
but probably not orthogonal.
