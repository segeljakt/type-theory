<h1 align="center">Typed λ-calculus in Rust</h1>

This project is both a playground for experimenting with type theory, and a reference for how one can implement a functional programming language compiler in Rust.

# Testing

You can run the examples as follows:

```bash
cargo run --example=end-to-end
```

```
- :: (int → int)
+ :: (int → (int → int))

5
Inferred type: int

"hello"
Inferred type: str

true
Inferred type: bool

((+ 1) 2)
Inferred type: int

((+ true) false)
Error: Cannot unify `int` with `bool`

let id = λx.(x x) in id
Error: `'t0` and `('t0 → 't1)` are recursive

...
```


Planned/finished features are:

# Front-end

- [x] Lexing ([regex](https://crates.io/crates/regex))
- [x] Parsing ([LALRPOP](https://crates.io/crates/lalrpop))
- [ ] Uniquify ([De-Brujin Indices](https://en.wikipedia.org/wiki/De_Bruijn_index))
- [x] Bi-directional type inference ([Hindley-Milner, Algorithm W](https://en.wikipedia.org/wiki/Hindley%E2%80%93Milner_type_system))
- [ ] Normalization
- [ ] Type classes

# Quality of life:

- [x] Pretty printing
- [x] Error recovery
- [ ] Language Server Protocol integration ([LSP](https://langserver.org/) using [codespan](https://docs.rs/codespan/0.3.0/codespan/))

# Middle-end

N/A

# Back-end

N/A

# Learning resources

* [Ionut G. Stan: Let’s write a type checker @ I T.A.K.E. Unconference 2015](https://www.youtube.com/watch?v=oPVTNxiMcSU)
* [A basic implementation of Hindley-Milner type inference via Algorithm W in Rust.](https://github.com/nwoeanhinnogaehr/algorithmw-rust)
* [f(by) 2019 - Christoph Hegemann, TYPE INFERENCE FROM SCRATCH](https://www.youtube.com/watch?v=ytPAlhnAKro)
