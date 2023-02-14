# How to make ad-hoc polymorphism less ad hoc

## Introduction

**Ad-hoc polymorphism** occurs when a function is defined and acts differently
for several types. For example, overloading.

**Parametric polymorphism** occurs when a function is defined and acts the same
for a range of types. Hindley-Milner is commonly accepted.

**Type classes** extend the Hindley-Milner type system, to include certain kinds
of overloading and unify the two types of polymorphism. During inference, a
program with type classes can be converted to an equivalent HM program without
overloading.

## Limitations of ad-hoc polymorphism

Expansion of ad-hoc polymorphic functions to the variants can lead to
exponential growth (multiply numbers of variants for each polymorphic type used
in a function).

Polymorphic equality has two objects of the same type, so the dictionary
pointers would redundant, if passed by instance. Remark: Like Java.

## An introductory example

This looks like traits in Rust and resembles Java-style interfaces.

## Translation

Class declarations are translated to a method dictionary with functions to
access the methods in the dictionary. The compiler can perform beta reductions
to transform those into the implemented methods.

## Subclasses

A type class can be defined as a subclass of another. Like Rust trait
inheritance or Java interface inheritance.

Having multiple superclasses is possible:

```haskell
class Top a where
  fun1 :: a -> a

class Top a => Left a where
  fun2 :: a -> a

class Top a => Right a where
  fun3 :: a -> a

class Left a, Right a => Bottom a where
  fun4 :: a -> a
```

The appropriate dictionaries are simply passed at run-time and no special
hashing schemes are required.

Question: Can I express this example with Rust traits? Yes!

## Conclusion

Assertions could possibly be added to class declarations, specifying properties
that each instance must satisfy.

Question: Has this been explored? This sounds like how `Module Type`s in Coq can
define lemmas as parameters, which instances supply, to prove that properties
hold on the type. Coq `Module Type`s probably postdate type classes as the first
Coq release was four months after this paper and it would not have been
feature-complete.

Unrestricted overloading of constants leads to situations where the overloading
can't be resolved without extra type information.

Remark: I think this is mitigated in Rust, by prefixing trait-associated
constants with the implementing trait's name, so resolution can proceed when
dealing with instances. In definitions within the trait, its own name is used as
a prefix and is unambiguous.

Type classes can be thought of as a kind of abstract data type, that specifies a
collection of functions and their types, but not their implementations. A type
class corresponds to an ADT with many implementations, one for each instance
declaration.

A drawback is that it introduces new parameters for method dictionaries in each
function that passes type classes. PE can specialize for certain dictionaries.

Question: Does this predate C++ vtables? Type class method dictionaries are very
similar, except vtables are stored in every instance.
