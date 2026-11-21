# Strassen's algorithm, fast inversion and fast nested dissection, in Lean 4

A Lean 4 and Mathlib formalization of Strassen's algorithm, inversion and determinants of matrices
with nonzero leading principal minors in `O(M(n))` arithmetic operations, and nested dissection with
fast matrix multiplication on plane graphs in `O(n^(ω/2))` operations, with every operation counted.
All proofs use only the axioms `propext`, `Classical.choice` and `Quot.sound`.

Author and maintainer: Robert D. Barish ([rbarish@ims.u-tokyo.ac.jp](mailto:rbarish@ims.u-tokyo.ac.jp)).

## Submission

| Challenge | Solution | Comparator configuration | Metadata | Theorems |
|---|---|---|---|---|
| `FastGEChallenge.lean` | `FastGESolution.lean` | `comparator.json` | `formalization.yaml` | 6 |

The Challenge module is the statement to audit: it is self-contained, imports only Mathlib and ends
with the compared theorems proved by `sorry`. The Solution module imports the libraries of this
repository, never the Challenge. The configuration permits exactly the axioms `propext`,
`Quot.sound` and `Classical.choice`, compares no definitions separately (`definition_names` is
empty) and enables nanoda. The definitions in the Challenge are copies of the specification modules
of the libraries (`FastGE/Spec.lean`, `Kasteleyn/Spec.lean`, `NestedDissection/Spec.lean`,
`PlanarSeparator/Spec.lean`, `WordRAM/AlgebraicSpec.lean`, `WordRAM/Spec.lean`); the comparator
checks that every constant used by the compared statements is the same kernel constant in the
Solution's environment.

## Statement

### Common definitions

**The arithmetic model (`WordRAM.Algebraic`).** `Counted α` is the writer monad over
`OpCount = (adds, muls)`: a value together with the number of additive operations (additions,
subtractions, negations) and of multiplications performed through the charged primitives `Op.add`,
`Op.sub`, `Op.neg`, `Op.mul` (and `NestedDissection.opInv`, an inversion charged as one
multiplication). `cost.total = adds + muls`. Moving, copying, padding and reindexing data costs
nothing. The algorithms whose costs are stated are defined explicitly in the Challenges, and their
definitions are part of the statements.

**Plane graphs as rotation systems (`Kasteleyn.RotationSystem`).** For a Mathlib simple graph `G`
(no loops, no multiple edges), a rotation system is a permutation `rot` of the darts of `G` that
keeps the initial vertex and permutes the darts leaving each vertex in a single cycle. The face
permutation sends a dart `d` to `rot (d.symm)`; the faces are its cycles, and the face of a dart is
the cycle containing it. The rotation system is *plane* (`IsPlane`) if `G` is connected and
`|V| + |faces| = |E| + 2` (Euler's formula). That such rotation systems are exactly the
combinatorial types of plane embeddings is classical and not formalized. Since faces are cycles of
darts, the one-vertex graph has no faces and is not plane in this sense: every statement assuming
`IsPlane` is about a connected graph with at least one edge.

### Fast Gaussian elimination (`FastGEChallenge.lean`)

The three nested-dissection statements assume `IsPlane`, so they are about connected graphs with at
least one edge; the disconnected case is not formalized.

Strassen's algorithm, its exponent, and inversion with the determinant by recursive block
elimination for matrices with nonzero leading principal minors are from Strassen (1969); the bound
in terms of an arbitrary multiplication algorithm follows Bunch and Hopcroft (1974), whose pivoting
for general invertible matrices is not formalized. Nested dissection with fast matrix multiplication
in `O(n^(ω/2))` operations is from Lipton, Rose and Tarjan (1979) and Pan and Reif (1993). The
explicit constants are those of this formalization; the cases of squares of plane graphs of bounded
degree and of positive definite matrices are derived here (the latter because every principal minor
of a positive definite matrix is positive, so `NodeRegular` holds at every node).

Definitions: a `MatMulAlgorithm R` is a counted procedure `mul n A B` for `n × n` matrices with
proofs that it returns `A * B` and performs at most `bound n` operations, `bound` monotone;
`HasExponent ω C`: `bound n ≤ C n^ω` for `n ≥ 1`. `Strassen.strassen k` is Strassen's recursion on
matrices of size `2^k` (seven recursive products, eighteen block additions or subtractions, a
`1 × 1` product costs one multiplication); `strassenPad` pads with zeros to size `2^⌈log₂ n⌉`;
`ω₀ = log₂ 7`. `FastDet.invDet alg A` runs block inversion (two recursive inversions, six products
by `alg`, the Schur complement) on `diag(A, 1)` of size `2^⌈log₂ n⌉` and returns the pair (inverse,
determinant). `ndCounted G alg A t` is block elimination along the separator tree `t` (frontal
matrices on the boundary sets, products by `alg`); `NodeRegular A t` says that for every initial
segment `s'` of the root separator the principal submatrix of `A` on the vertices of the two
subtrees together with `s'` is invertible. In the statements, "the two growth conditions" are
`4 · bound (2^k) ≤ bound (2^(k+1))` for all `k` and `1 ≤ bound 1`. A separator tree (`SepTree`) is a
leaf holding a vertex set or a node holding a separator and two subtrees; `t.verts` is the union of
all its sets, and `IsDissection G t` says that at every node the separator and the vertex sets of
the two subtrees are pairwise disjoint and no edge of `G` joins the two subtrees. A separator tree
of `G` covering all vertices is one with `IsDissection G t` and `t.verts = univ`. `square G` joins
distinct vertices at distance at most 2.

* `FastGE.strassen_count`: over every ring and for all matrices of size `2^k`, `strassen k A B`
  returns `A * B` with cost exactly `(adds, muls) = (6 (7^k - 4^k), 7^k)`.
* `FastGE.strassen_exponent`: `2 < ω₀ < 3`, and over every ring there is a `MatMulAlgorithm` whose
  procedure is `strassenPad`, with `HasExponent ω₀ 49` and the two growth conditions.
* `FastGE.inverse_determinant`: over every field, for every `MatMulAlgorithm` with the two growth
  conditions and every `n × n` matrix `A`: if all leading principal minors are nonzero,
  `invDet alg A` returns `(A⁻¹, det A)`; always its cost satisfies
  `cost + 1 ≤ 5 · bound (2^⌈log₂ n⌉)`; and if `ω ≥ 0`, `HasExponent ω C` and `n ≥ 1`, the cost is at
  most `5 C 2^ω n^ω`.
* `FastGE.planar_fast_determinant`: over every field, for every `MatMulAlgorithm` with the two
  growth conditions and `HasExponent ω C`, `ω > 2`, and every plane graph `G` on `Fin n`, there is a
  separator tree `t` of `G` covering all vertices such that for every matrix `A` whose off-diagonal
  nonzero entries are edges of `G` and with `NodeRegular A` at every node, `ndCounted G alg A t`
  returns `det A` with at most `(5 C 2^ω + 2C + 2) (2T + 1)^ω / (1 - (2/3)^(ω/2 - 1)) · n^(ω/2)`
  operations, `T = 50000`.
* `FastGE.square_fast_determinant`: the same for `square G`, `G` plane of maximum degree at most
  `Δ`, with `T = 40 (1062 (Δ + 1)² + 1)`.
* `FastGE.square_fast_determinant_posDef`: the same as `FastGE.square_fast_determinant` over a field
  with a partial order and a star structure (`IsOrderedRing`, `PosMulReflectLT`, `StarRing`; for
  instance `ℝ`), for positive definite `A`, without the hypothesis `NodeRegular`.

## Libraries

Each library root module (`WordRAM.lean`, …) imports the modules of the library present here. The
libraries contain exactly the modules needed by the Solution (37 modules).

| Library | Modules | Content |
|---|---|---|
| `WordRAM` | 3 | the counted-operation model |
| `Kasteleyn` | 3 | rotation systems and faces |
| `NestedDissection` | 9 | separator trees, fill, sparse elimination |
| `PlanarSeparator` | 12 | the planar separator theorem and separator trees |
| `FastGE` | 10 | Strassen multiplication, block inversion, fast nested dissection |

`Audit.lean` prints the axioms of the 6 compared theorems and of 23 further theorems of the
libraries.

## Checking

Toolchain `leanprover/lean4:v4.35.0-rc2`; Mathlib as pinned in `lakefile.toml` and
`lake-manifest.json`.

```bash
lake exe cache get && lake build
lake env lean Audit.lean    # every report names only propext, Classical.choice, Quot.sound
lake comparator --config comparator.json --paranoid
```

`lake comparator` needs `bwrap` and the toolchain's `bin` directory on `PATH`.

## License

Apache-2.0 (`LICENSE`).
