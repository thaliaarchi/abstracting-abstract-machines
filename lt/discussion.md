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

## 2023-03-16

### Topic 1

They combine linear and non-linear types, with the restrictions that non-linear
structures must not contain any non-linear components and that non-linear
functions may only be introduced in environments containing only non-linear
types. This would seem to imply that linear types must be at the top level in
a combined system. If this was extended to support all substructural type
systems, what would it look like?

As stated on [Wikipedia](https://en.wikipedia.org/wiki/Substructural_type_system),
the substructural type systems are:

|          | Exchange | Weakening | Contraction | Use                   |
| -------- | -------- | --------- | ----------- | --------------------- |
| Ordered  | —        | —         | —           | Exactly once in order |
| Linear   | Allowed  | —         | —           | Exactly once          |
| Affine   | Allowed  | Allowed   | —           | At most once          |
| Relevant | Allowed  | —         | Allowed     | At least once         |
| Normal   | Allowed  | Allowed   | Allowed     | Arbitrarily           |

Would this then be the hierarchy of embedding?

```dot
digraph {
  ordered -> linear;
  linear -> affine;
  linear -> relevant;
  affine -> normal;
  relevant -> normal;
}
```
