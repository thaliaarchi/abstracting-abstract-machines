//! # Simply-typed lambda calculus (λ→)
//!
//! Notation changes:
//!
//! - : instead of :: for type annotations
//! - ⇐ instead of ::↓ for type checking
//! - ⇒ instead of ::↑ for type inference

use std::collections::{HashMap, HashSet};

/// Base type: α
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct TypeId(u32);

/// Variable: x
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Var(u32);

/// The type language of λ→: τ
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Type {
    /// Base type: α
    Base(TypeId),
    /// Function type: τ → τ′
    Func(Box<Type>, Box<Type>),
}

/// The kinds of terms: e
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Term {
    /// Annotated term: e : τ
    Anno(Box<Term>, Box<Type>),
    /// Variable: x
    Var(Var),
    /// Application: e e′
    App(Box<Term>, Box<Term>),
    /// Lambda abstraction: λx → e
    Lam(Var, Box<Term>),
}

/// Values: v
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Val {
    /// Neutral term: n ::= x | n v
    /// (A variable applied to a sequence of values)
    Neut(Var, Vec<Val>),
    /// Lambda abstraction: λx → v
    Lam(Var, Box<Val>),
}

// Contexts: Γ
pub struct Ctx {
    /// Adding a type identifier: Γ, α : *
    pub base_types: HashSet<TypeId>,
    /// Adding a term identifier: Γ, x : τ
    pub terms: HashMap<Var, Box<Type>>,
}
