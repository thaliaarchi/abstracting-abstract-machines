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

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Name {
    Global(String),
    Local(Var),
    Quote(Var),
}

/// Inferrable terms (Term↑)
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TermInf {
    /// Annotated term: e : τ
    Ann(Box<TermChk>, Box<Type>),
    /// Variable: x
    Bound(Var),
    /// Variable: x
    Free(Name),
    /// Application: e e′
    App(Box<TermInf>, Box<TermChk>),
}

/// Checkable terms (Term↓)
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TermChk {
    /// Embedded inferrable term
    Inf(Box<TermInf>),
    /// Lambda abstraction: λx → e
    Lam(Box<TermChk>),
}

/// The type language of λ→: τ
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Type {
    /// Base type: α
    Free(Name),
    /// Function type: τ → τ′
    Fun(Box<Type>, Box<Type>),
}

/// Values: v
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Value {
    /// Neutral term: n
    Neutral(Neutral),
    /// Lambda abstraction: λx → v
    Lam(Box<Value>, Box<Value>),
}

/// Neutral term: n
/// (A variable applied to a sequence of values)
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Neutral {
    /// Variable: x
    Free(Name),
    /// Application: n v
    App(Box<Neutral>, Box<Value>),
}

impl Value {
    pub fn free(n: Name) -> Self {
        Value::Neutral(Neutral::Free(n))
    }
}

// Contexts: Γ
pub struct Ctx {
    /// Adding a type identifier: Γ, α : *
    base_types: HashSet<TypeId>,
    /// Adding a term identifier: Γ, x : τ
    terms: HashMap<Var, Box<Type>>,
}
