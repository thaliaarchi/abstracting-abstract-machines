# Gradual typestate

## Topic 2

I envision an easy introduction of powerful typestates into Rust, by leveraging
its borrowing rules. The paper's terminology has a close, but not exact
translation to Rust. `full` is defined as having exclusive write access,
`shared` has shared write access, and `pure` has shared, read-only access.
Rust's `T` is owned, so has exclusive access, `&mut T` has exclusive write
access, and `&T` has shared, read-only access. Rust's stricter semantics forbid
interfering writes, but I don't think that gets in the way of implementing
typestates.

`OpenFile` and `ClosedFile` can easily be expressed with this pattern:

```rust
type OpenFile(File);
// OpenFile
// &mut OpenFile
// &OpenFile

type ClosedFile(PathBuf);
// ClosedFile
// &mut ClosedFile
// &ClosedFile
```
