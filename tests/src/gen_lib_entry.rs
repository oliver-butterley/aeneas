//@ [!lean] skip
//@ [lean] aeneas-args=-split-files -gen-lib-entry
//! Exercises the `-gen-lib-entry` writer: with `-split-files -gen-lib-entry`
//! Aeneas emits a crate entry-point file (`GenLibEntry.lean`) that imports the
//! split `.Funs` module and places the split modules in the `GenLibEntry/`
//! sub-folder. This is the only test covering that writer path.

pub fn f(x: u32) -> u32 {
    x + 1
}

pub fn g(x: u32) -> u32 {
    f(x) + 1
}
