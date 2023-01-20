# Collapsing Towers of Interpreters

## Introduction

Presents a multi-level lambda calculus that features staging constructs and
stage polymorphism, i.e., based on runtime parameters, an evaluator either
executes source code or generates code.

Without loss of generality, they restrict the scope to interpreters based on
variations of the lambda calculus. **Question:** Their lambda calculus or just
regular lambda calculus? How could I support my favorite stranger languages?

They consider reflective interpreters (can be inspected and modified at runtime)
and conceptually infinite self-interpretation.

Examples:
- A base VM executing an evaluator executing a regex matcher (VM, evaluator,
  regex matcher) collapsed to VM code for that regex
- User-modified semantics: A base VM executing an evaluator executing a modified
  evaluator executing a user program. The modified evaluator can, for example,
  add tracing or counting of variable accesses or be written in CPS. Under
  modified semantics, interpreters become program transformers.

Staging an interpreter yields a compiler. However, trying to stage all
intermediate interpreters individually requires each intermediate language to
have dedicated codegen capabilities targeting the next language and this
produces a multi-pass compiler, instead of single-pass, so it cannot work for
reflective towers, where language delineations are fuzzy and execution may jump
between levels.

They approach this through abstracting over staging decisions using stage
polymorphism. To collapse interpreters L_0, ..., L_n, they start with a
multi-level language L_0 (a language that has built-in staging operators) and
express all other evaluators so they're stage polymorphic (able to act either as
an interpreter or translator). All intermediate interpreters L_1, ..., L_n-1
pass through staging commands from L_n, but do not execute any staging commands
of their own. As a result, only staging commands from the top-level user program
lead to code generation commands.

The idea for stage polymorphism was inspired by high-performance program
generators for numeric libraries. **Aside:** Maybe read “A Stage-Polymorphic IR
for Compiling MATLAB-Style Dynamic Tensor Expressions” (Stojanov, Rompf, and
Püschel 2019), which uses Lightweight Modular Staging for tensors in Matlab.

Languages:
- λ⇅: multi-level kernel language, that supports staging through polymorphic
  `Lift` operator and stage polymorphism through dynamic operator overloading.
- Pink: a restricted Lisp front-end with a meta-circular evaluator.
- Purple: every aspect of semantics can change dynamically. Is implemented on
  top of Lightweight Modular Staging. **Read this**.

**Summary:** Collapsing Towers of Interpreters presents a lambda calculus, with
which multiple levels of interpretation can be collapsed into code generated for
the base language. They approach this using stage polymorphism, where an
evaluator can act as either an interpreter or a translator. Through this, only
staging commands from the top-level user program lead to code generation
commands and intermediate interpreters pass through staging commands from upper
interpreters, while not executing any staging commands of their own. They
support reflectively modified interpreters and self-interpretation.

## Preliminaries

Interpreters and compilers are linked through specialization, as formalized in
the three Futamura projections (Futamura 1971, 1999).
