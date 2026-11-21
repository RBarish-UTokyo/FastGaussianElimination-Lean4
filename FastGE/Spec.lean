module

public import NestedDissection.Spec
public import Kasteleyn.Spec
public import Mathlib.Data.Matrix.Block
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Data.Nat.Log
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Data.Matrix.ColumnRowPartitioned

/-!
# Specification: fast matrix multiplication, inversion, and nested dissection

This file is the authoritative statement of the `FastGE` entry. It imports only Mathlib and the
Mathlib-only specification modules `WordRAM/AlgebraicSpec.lean` (the counting monad),
`NestedDissection/Spec.lean` (separator trees, the filled graph, squares of graphs) and
`Kasteleyn/Spec.lean` (rotation systems and plane rotation systems; only its section `Map` is
used). The development imports this file, so the theorems of the library are about exactly these
constants. `Challenge.lean` contains a generated, self-contained copy,
followed by the targets with `sorry`.

## The cost model

All algorithms are written in the counting monad `WordRAM.Algebraic.Counted`: the cost of a
computation is the number of ring operations performed through the charged primitives (`Op.add`,
`Op.sub`, `Op.neg`, `Op.mul`, `Mat.add`, `Mat.sub`, `NestedDissection.opInv`, which charges one
multiplication for an inversion). Data movement is free. A cost statement is about the explicit
algorithm defined below, and the reader checks, by reading these definitions, that every ring
operation on matrix entries goes through a charged primitive.

A matrix multiplication algorithm (`MatMulAlgorithm`) bundles a procedure in the monad with
proofs that it computes the product and performs at most `bound n` operations on `n × n`
matrices. Algorithms built on it (`FastDet.invDet`, `FastDissection.ndCounted`) call its procedure
for every product, so their costs include the costs of these calls: the statements bound the cost
in terms of `bound`, i.e. in `O(M(n))`.

## Contents

* `MatMulAlgorithm`, `MatMulAlgorithm.HasExponent` (`bound n ≤ C n ^ ω` for `n ≥ 1`).
* Strassen's algorithm: `Strassen.strassen` on matrices of size `2 ^ k` (block splitting
  `Strassen.split`, `Strassen.join`), `Strassen.strassenPad` on `n × n` matrices, padded with
  zeros to the next power of two (`Pad.pad`, `Pad.unpad`), and `Strassen.strassenExponent`
  `= log₂ 7`.
* Block inversion: `BlockInverse.invDet` on matrices of size `2 ^ k`, and `FastDet.invDet` on
  `n × n` matrices, through `diag(A, 1)` of size `2 ^ ⌈log₂ n⌉` (`FastDet.padOne`).
* Block elimination along a separator tree: the frontal step `Frontal.frontStep` (with the
  rectangular product `Frontal.rectMul`) and `FastDissection.ndCounted`; the regularity
  hypothesis `FastDissection.NodeRegular`.
* The targets: `StrassenCount`, `StrassenExponent`, `InverseDeterminant`,
  `PlanarFastDeterminant`, `SquareFastDeterminant` and `SquareFastDeterminantPosDef`.

`Strassen.le_two_pow_clog` (`n ≤ 2 ^ ⌈log₂ n⌉`) is the only lemma: the padded algorithms use it.

Mucha and Sankowski's algorithm for maximum matchings in planar graphs, which uses this
elimination, is not formalized.
-/

@[expose] public section

namespace FastGE

open WordRAM.Algebraic

universe u

/-! ### Matrix multiplication algorithms -/

/-- A matrix multiplication algorithm over `R` in the arithmetic cost model: a procedure
computing the product of two `n × n` matrices, together with a monotone bound on the number of
ring operations it performs. -/
structure MatMulAlgorithm (R : Type u) [Ring R] where
  /-- The multiplication procedure. -/
  mul : (n : ℕ) → SqMat n R → SqMat n R → Counted (SqMat n R)
  /-- The procedure computes the matrix product. -/
  mul_val : ∀ (n : ℕ) (A B : SqMat n R), (mul n A B).val = A * B
  /-- Bound on the number of operations for inputs of size `n`. -/
  bound : ℕ → ℕ
  /-- The bound is monotone in the size. -/
  bound_mono : Monotone bound
  /-- The procedure performs at most `bound n` operations on inputs of size `n`. -/
  cost_le : ∀ (n : ℕ) (A B : SqMat n R), (mul n A B).cost.total ≤ bound n

namespace MatMulAlgorithm

variable {R : Type u} [Ring R]

/-- `alg` runs within `C * n ^ ω` operations on all inputs of size `n ≥ 1`. -/
def HasExponent (alg : MatMulAlgorithm R) (ω C : ℝ) : Prop :=
  ∀ n : ℕ, 1 ≤ n → (alg.bound n : ℝ) ≤ C * (n : ℝ) ^ ω

end MatMulAlgorithm

/-! ### Strassen's algorithm -/

namespace Strassen

variable {R : Type u}

/-- Splitting `Fin (2 ^ (k + 1))` into its first and its second half. -/
def halves (k : ℕ) : Fin (2 ^ (k + 1)) ≃ Fin (2 ^ k) ⊕ Fin (2 ^ k) :=
  (finCongr (Nat.two_pow_succ k)).trans finSumFinEquiv.symm

/-- View a matrix of size `2 ^ (k + 1)` as a `2 × 2` block matrix with blocks of size
`2 ^ k`. -/
def split {k : ℕ} (A : SqMat (2 ^ (k + 1)) R) :
    Matrix (Fin (2 ^ k) ⊕ Fin (2 ^ k)) (Fin (2 ^ k) ⊕ Fin (2 ^ k)) R :=
  Matrix.reindex (halves k) (halves k) A

/-- Assemble four blocks of size `2 ^ k` into a matrix of size `2 ^ (k + 1)`. -/
def join {k : ℕ} (C₁₁ C₁₂ C₂₁ C₂₂ : SqMat (2 ^ k) R) : SqMat (2 ^ (k + 1)) R :=
  (Matrix.reindex (halves k) (halves k)).symm (Matrix.fromBlocks C₁₁ C₁₂ C₂₁ C₂₂)

/-- Strassen's recursive multiplication of two matrices of size `2 ^ k`, in the counting
monad.  A `1 × 1` product costs one multiplication; a product of size `2 ^ (k + 1)` makes
seven recursive products of size `2 ^ k` and eighteen block additions/subtractions. -/
def strassen [Ring R] : (k : ℕ) → SqMat (2 ^ k) R → SqMat (2 ^ k) R → Counted (SqMat (2 ^ k) R)
  | 0, A, B => do
      let c ← Op.mul (A ⟨0, Nat.two_pow_pos 0⟩ ⟨0, Nat.two_pow_pos 0⟩)
        (B ⟨0, Nat.two_pow_pos 0⟩ ⟨0, Nat.two_pow_pos 0⟩)
      pure (Matrix.of fun _ _ => c)
  | k + 1, A, B => do
      let A₁₁ := (split A).toBlocks₁₁
      let A₁₂ := (split A).toBlocks₁₂
      let A₂₁ := (split A).toBlocks₂₁
      let A₂₂ := (split A).toBlocks₂₂
      let B₁₁ := (split B).toBlocks₁₁
      let B₁₂ := (split B).toBlocks₁₂
      let B₂₁ := (split B).toBlocks₂₁
      let B₂₂ := (split B).toBlocks₂₂
      -- the seven products, with ten block additions/subtractions
      let S₁ ← Mat.add A₁₁ A₂₂
      let T₁ ← Mat.add B₁₁ B₂₂
      let M₁ ← strassen k S₁ T₁
      let S₂ ← Mat.add A₂₁ A₂₂
      let M₂ ← strassen k S₂ B₁₁
      let T₃ ← Mat.sub B₁₂ B₂₂
      let M₃ ← strassen k A₁₁ T₃
      let T₄ ← Mat.sub B₂₁ B₁₁
      let M₄ ← strassen k A₂₂ T₄
      let S₅ ← Mat.add A₁₁ A₁₂
      let M₅ ← strassen k S₅ B₂₂
      let S₆ ← Mat.sub A₂₁ A₁₁
      let T₆ ← Mat.add B₁₁ B₁₂
      let M₆ ← strassen k S₆ T₆
      let S₇ ← Mat.sub A₁₂ A₂₂
      let T₇ ← Mat.add B₂₁ B₂₂
      let M₇ ← strassen k S₇ T₇
      -- the four result blocks, with eight block additions/subtractions
      let U₁ ← Mat.add M₁ M₄
      let U₂ ← Mat.sub U₁ M₅
      let C₁₁ ← Mat.add U₂ M₇
      let C₁₂ ← Mat.add M₃ M₅
      let C₂₁ ← Mat.add M₂ M₄
      let V₁ ← Mat.sub M₁ M₂
      let V₂ ← Mat.add V₁ M₃
      let C₂₂ ← Mat.add V₂ M₆
      pure (join C₁₁ C₁₂ C₂₁ C₂₂)

end Strassen

namespace Pad

variable {R : Type u} {n N : ℕ}

/-- Splitting `Fin N` into the first `n` indices and the remaining `N - n`. -/
def equiv (h : n ≤ N) : Fin N ≃ Fin n ⊕ Fin (N - n) :=
  (finCongr (Nat.add_sub_cancel' h).symm).trans finSumFinEquiv.symm

/-- Embed an `n × n` matrix as the upper left block of an `N × N` matrix, zeros elsewhere. -/
def pad [Zero R] (h : n ≤ N) (A : SqMat n R) : SqMat N R :=
  (Matrix.reindex (equiv h) (equiv h)).symm (Matrix.fromBlocks A 0 0 0)

/-- The upper left `n × n` block of an `N × N` matrix. -/
def unpad (h : n ≤ N) (C : SqMat N R) : SqMat n R :=
  (Matrix.reindex (equiv h) (equiv h) C).toBlocks₁₁

end Pad

namespace Strassen

variable {R : Type u} [Ring R]

/-- The padded size used by `strassenPad` is enough. -/
theorem le_two_pow_clog (n : ℕ) : n ≤ 2 ^ Nat.clog 2 n :=
  Nat.le_pow_clog one_lt_two n

/-- Strassen's algorithm for `n × n` matrices: pad with zeros to size `2 ^ Nat.clog 2 n`, the
least power of two that is at least `n`, multiply, and extract the upper left block. -/
def strassenPad (n : ℕ) (A B : SqMat n R) : Counted (SqMat n R) :=
  Pad.unpad (le_two_pow_clog n) <$>
    strassen (Nat.clog 2 n) (Pad.pad (le_two_pow_clog n) A) (Pad.pad (le_two_pow_clog n) B)

/-- The exponent `ω₀ = log₂ 7 ≈ 2.807` of Strassen's algorithm. -/
noncomputable def strassenExponent : ℝ := Real.logb 2 7

end Strassen

/-! ### Block inversion -/

section Inverse

open Matrix

namespace BlockInverse

variable {K : Type u}

/-- Entrywise negation, one additive operation per entry. -/
def matNeg [Neg K] {m n : Type*} [Fintype m] [Fintype n] (A : Matrix m n K) :
    Counted (Matrix m n K) :=
  Counted.pi fun i => Counted.pi fun j => Op.neg (A i j)

/-- The only index of a matrix of size `2 ^ 0`. -/
def idx0 : Fin (2 ^ 0) := ⟨0, Nat.two_pow_pos 0⟩

variable [Field K]

/-- Block inversion: the pair `(M⁻¹, det M)` for a matrix `M` of size `2 ^ k`, with all products
computed by `alg`.  A `1 × 1` matrix costs one inversion; a matrix of size `2 ^ (k + 1)` makes
two recursive calls, six products of size `2 ^ k`, four entrywise block operations and one
scalar multiplication. -/
def invDet (alg : MatMulAlgorithm K) :
    (k : ℕ) → SqMat (2 ^ k) K → Counted (SqMat (2 ^ k) K × K)
  | 0, M => do
      let b ← NestedDissection.opInv (M idx0 idx0)
      pure (Matrix.of fun _ _ => b, M idx0 idx0)
  | k + 1, M => do
      let A := (Strassen.split M).toBlocks₁₁
      let B := (Strassen.split M).toBlocks₁₂
      let C := (Strassen.split M).toBlocks₂₁
      let D := (Strassen.split M).toBlocks₂₂
      -- the leading block
      let r₁ ← invDet alg k A
      -- the Schur complement `S = D - (C A⁻¹) B`
      let X ← alg.mul (2 ^ k) C r₁.1
      let Y ← alg.mul (2 ^ k) X B
      let S ← Mat.sub D Y
      let r₂ ← invDet alg k S
      -- the four blocks of the inverse
      let Z ← alg.mul (2 ^ k) r₁.1 B
      let W ← alg.mul (2 ^ k) Z r₂.1
      let V ← alg.mul (2 ^ k) W X
      let T ← Mat.add r₁.1 V
      let U ← alg.mul (2 ^ k) r₂.1 X
      let W' ← matNeg W
      let U' ← matNeg U
      let d ← Op.mul r₁.2 r₂.2
      pure (Strassen.join T W' U' r₂.1, d)

end BlockInverse

namespace FastDet

open NestedDissection

variable {K : Type u} [Field K]

section Pad

variable {n N : ℕ}

/-- The matrix `diag(A, 1)` of size `N ≥ n`, with `A` as its leading block. -/
def padOne (h : n ≤ N) (A : SqMat n K) : SqMat N K :=
  (reindex (Pad.equiv h) (Pad.equiv h)).symm (fromBlocks A 0 0 1)

end Pad

/-- Inverse and determinant of an `n × n` matrix by block inversion of `diag(A, 1)` of size
`2 ^ ⌈log₂ n⌉`, with all products computed by `alg`. -/
def invDet (alg : MatMulAlgorithm K) {n : ℕ} (A : SqMat n K) : Counted (SqMat n K × K) :=
  (fun r => (Pad.unpad (Strassen.le_two_pow_clog n) r.1, r.2)) <$>
    BlockInverse.invDet alg (Nat.clog 2 n) (padOne (Strassen.le_two_pow_clog n) A)

end FastDet

end Inverse

/-! ### Block elimination along a separator tree -/

namespace Frontal

open Matrix

section Schur

variable {V : Type} [DecidableEq V] {K : Type u} [Field K]

/-- The principal submatrix `A[W, W]`. -/
abbrev principal (A : Matrix V V K) (W : Finset V) : Matrix W W K := A.submatrix (↑) (↑)

end Schur

section RectMul

variable {K : Type u} [Field K]

/-- Embed a `p × q` matrix as the upper left block of an `m × m` matrix, zeros elsewhere. -/
def embed (m : ℕ) {p q : ℕ} (A : Matrix (Fin p) (Fin q) K) : SqMat m K :=
  Matrix.of fun i j => if h : (i : ℕ) < p ∧ (j : ℕ) < q then A ⟨i, h.1⟩ ⟨j, h.2⟩ else 0

/-- Rectangular multiplication by padding to size `m` with zeros. -/
def rectMul (alg : MatMulAlgorithm K) (m : ℕ) {p q r : ℕ} (hp : p ≤ m) (hr : r ≤ m)
    (A : Matrix (Fin p) (Fin q) K) (B : Matrix (Fin q) (Fin r) K) :
    Counted (Matrix (Fin p) (Fin r) K) :=
  (fun M => M.submatrix (Fin.castLE hp) (Fin.castLE hr)) <$> alg.mul m (embed m A) (embed m B)

end RectMul

section Front

variable {V : Type} [LinearOrder V] {K : Type u} [Field K]

/-- The `i`-th smallest element of `s`. -/
def pt (s : Finset V) (i : Fin s.card) : V := (s.orderIsoOfFin rfl i : V)

/-- The position of an element of `s` in increasing order. -/
def idx (s : Finset V) {x : V} (hx : x ∈ s) : Fin s.card := (s.orderIsoOfFin rfl).symm ⟨x, hx⟩

/-- The first `j` elements of `s` in increasing order. -/
def initSeg (s : Finset V) (j : ℕ) : Finset V :=
  (Finset.univ.filter fun i : Fin s.card => (i : ℕ) < j).image (pt s)

/-- The frontal matrix entry `A x y - Fa x y - Fb x y`, two additive operations. -/
def entry (A Fa Fb : Matrix V V K) (x y : V) : Counted K := do
  let u ← Op.sub (A x y) (Fa x y)
  Op.sub u (Fb x y)

/-- The sum `Fa + Fb + R` on the positions `e i, e j`, two additive operations per entry. -/
def sumUpd (Fa Fb : Matrix V V K) {q : ℕ} (e : Fin q → V) (R : Matrix (Fin q) (Fin q) K) :
    Counted (Matrix (Fin q) (Fin q) K) :=
  Counted.pi fun i => Counted.pi fun j => do
    let u ← Op.add (Fa (e i) (e j)) (Fb (e i) (e j))
    Op.add u (R i j)

/-- One frontal step. -/
def frontStep (alg : MatMulAlgorithm K) (A Fa Fb : Matrix V V K) (da db : K)
    (s Bd : Finset V) : Counted (K × Matrix V V K) := do
  let P ← Counted.pi fun i : Fin s.card => Counted.pi fun j : Fin s.card =>
    entry A Fa Fb (pt s i) (pt s j)
  let Bm ← Counted.pi fun i : Fin s.card => Counted.pi fun j : Fin Bd.card =>
    entry A Fa Fb (pt s i) (pt Bd j)
  let Cm ← Counted.pi fun i : Fin Bd.card => Counted.pi fun j : Fin s.card =>
    entry A Fa Fb (pt Bd i) (pt s j)
  let r ← FastDet.invDet alg (Matrix.of P)
  let Q ← rectMul alg (s.card + Bd.card) (Nat.le_add_left _ _) (Nat.le_add_right _ _)
    (Matrix.of Cm) r.1
  let R ← rectMul alg (s.card + Bd.card) (Nat.le_add_left _ _) (Nat.le_add_left _ _) Q
    (Matrix.of Bm)
  let Fq ← sumUpd Fa Fb (pt Bd) R
  let d₀ ← Op.mul da db
  let d ← Op.mul d₀ r.2
  pure (d, Matrix.of fun x y =>
    if hx : x ∈ Bd then if hy : y ∈ Bd then Fq (idx Bd hx) (idx Bd hy) else 0 else 0)

end Front

end Frontal

namespace FastDissection

open Matrix NestedDissection NestedDissection.SepTree FastGE.Frontal

variable {V : Type} [Fintype V] [LinearOrder V] {K : Type u} [Field K]

/-- The vertices of the two parts of the root (none at a leaf). -/
def partVerts : SepTree V → Finset V
  | leaf _ => ∅
  | node _ a b => a.verts ∪ b.verts

/-- The block elimination at the root of `t` meets only invertible blocks: for every initial
segment `s'` of the separator, the principal submatrix on the parts of the root together with `s'`
is invertible. This holds at every node when all principal minors of `A` are nonzero, for instance
when `A` is positive definite (`FastDissection.allNodes_nodeRegular_of_forall`). -/
def NodeRegular (A : Matrix V V K) (t : SepTree V) : Prop :=
  ∀ j ≤ t.own.card, (principal A (partVerts t ∪ initSeg t.own j)).det ≠ 0

variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Block elimination along the separator tree `t`, with all products computed by `alg`.  It
returns the determinant of the principal submatrix on the vertices of `t` and the correction of
these vertices (supported on their boundary).  Subtrees without vertices cost nothing. -/
def ndCounted (alg : MatMulAlgorithm K) (A : Matrix V V K) :
    SepTree V → Counted (K × Matrix V V K)
  | leaf s => if s = ∅ then pure (1, 0) else frontStep alg A 0 0 1 1 s (bdry G s)
  | node s a b =>
    if (node s a b).verts = ∅ then pure (1, 0) else do
      let ra ← ndCounted alg A a
      let rb ← ndCounted alg A b
      frontStep alg A ra.2 rb.2 ra.1 rb.1 s (bdry G (node s a b).verts)

end FastDissection

/-! ### The targets -/

section Targets

open Matrix NestedDissection NestedDissection.SepTree FastDissection

/-- **Strassen's algorithm and its exact operation count** (Strassen 1969). Over every ring, for
matrices of size `2 ^ k`, `Strassen.strassen` computes the product with exactly `7 ^ k`
multiplications and `6 (7 ^ k - 4 ^ k)` additive operations. -/
def StrassenCount : Prop :=
  ∀ (R : Type u) [Ring R] (k : ℕ) (A B : SqMat (2 ^ k) R),
    (Strassen.strassen k A B).val = A * B ∧
      (Strassen.strassen k A B).cost = ⟨6 * (7 ^ k - 4 ^ k), 7 ^ k⟩

/-- **The exponent of Strassen's algorithm.** `2 < ω₀ < 3` for `ω₀ = log₂ 7`, and over every ring
the padded algorithm `Strassen.strassenPad` is the procedure of a matrix multiplication algorithm
with exponent `ω₀` and constant `49` (at most `49 n ^ ω₀` operations on `n × n` matrices,
`n ≥ 1`), whose bound `M` satisfies `4 M (2 ^ k) ≤ M (2 ^ (k + 1))` and `1 ≤ M 1`, the
hypotheses of the targets below. -/
def StrassenExponent : Prop :=
  (2 < Strassen.strassenExponent ∧ Strassen.strassenExponent < 3) ∧
    ∀ (R : Type u) [Ring R], ∃ alg : MatMulAlgorithm R, alg.mul = Strassen.strassenPad ∧
      alg.HasExponent Strassen.strassenExponent 49 ∧
      (∀ k, 4 * alg.bound (2 ^ k) ≤ alg.bound (2 ^ (k + 1))) ∧ 1 ≤ alg.bound 1

/-- **Inverse and determinant in `O(M(n))` operations** (Strassen 1969; Bunch and Hopcroft 1974
remove the condition on the minors by pivoting, which is not formalized). Let `alg` be a matrix
multiplication algorithm over a field whose bound `M` satisfies
`4 M (2 ^ k) ≤ M (2 ^ (k + 1))` and `1 ≤ M 1`. For an `n × n` matrix `A`, `FastDet.invDet alg A`
returns `(A⁻¹, det A)` when all leading principal minors of `A` are nonzero; it performs fewer
than `5 M (2 ^ ⌈log₂ n⌉)` operations, and at most `5 C 2 ^ ω n ^ ω` if `alg` has exponent
`ω ≥ 0` with constant `C` and `n ≥ 1`. -/
def InverseDeterminant : Prop :=
  ∀ (K : Type u) [Field K] (alg : MatMulAlgorithm K),
    (∀ k, 4 * alg.bound (2 ^ k) ≤ alg.bound (2 ^ (k + 1))) → 1 ≤ alg.bound 1 →
    ∀ {n : ℕ} (A : SqMat n K),
      ((∀ j hj, (leading A j hj).det ≠ 0) → (FastDet.invDet alg A).val = (A⁻¹, A.det)) ∧
      (FastDet.invDet alg A).cost.total + 1 ≤ 5 * alg.bound (2 ^ Nat.clog 2 n) ∧
      ∀ {ω C : ℝ}, 0 ≤ ω → alg.HasExponent ω C → 1 ≤ n →
        ((FastDet.invDet alg A).cost.total : ℝ) ≤ 5 * C * 2 ^ ω * (n : ℝ) ^ ω

/-- **Fast nested dissection for plane graphs** (Lipton, Rose and Tarjan 1979; Pan and Reif
1993). Let `alg` be a matrix multiplication algorithm over a field with exponent `ω > 2` and
constant `C`, whose bound `M` satisfies `4 M (2 ^ k) ≤ M (2 ^ (k + 1))` and `1 ≤ M 1`. For every
plane graph `G` on `Fin n` there is a separator tree `t` of `G` such that, for every matrix `A`
whose off-diagonal nonzero entries are edges of `G` and for which block elimination along `t` is
regular, block elimination along `t` computes `det A` with at most
`(5 C 2 ^ ω + 2 C + 2) (2 T + 1) ^ ω / (1 - (2/3) ^ (ω/2 - 1)) n ^ (ω / 2)` operations,
`T = 50000`.

As `IsPlane` requires, `G` is connected and has at least one edge. -/
def PlanarFastDeterminant : Prop :=
  ∀ (K : Type u) [Field K] (alg : MatMulAlgorithm K),
    (∀ k, 4 * alg.bound (2 ^ k) ≤ alg.bound (2 ^ (k + 1))) → 1 ≤ alg.bound 1 →
    ∀ {ω C : ℝ}, 2 < ω → alg.HasExponent ω C →
    ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (R : Kasteleyn.RotationSystem G),
      R.IsPlane →
      ∃ t : SepTree (Fin n), IsDissection G t ∧ t.verts = Finset.univ ∧
        ∀ A : Matrix (Fin n) (Fin n) K, (∀ x y, x ≠ y → A x y ≠ 0 → G.Adj x y) →
          AllNodes (NodeRegular A) t →
          (ndCounted G alg A t).val.1 = A.det ∧
            ((ndCounted G alg A t).cost.total : ℝ) ≤
              (5 * C * 2 ^ ω + 2 * C + 2) * (50000 + 50000 + 1) ^ ω /
                (1 - (2 / 3 : ℝ) ^ (ω / 2 - 1)) * (n : ℝ) ^ (ω / 2)

/-- **Fast nested dissection for squares of plane graphs of bounded degree.** As
`PlanarFastDeterminant`, for the square of a plane graph `G` of maximum degree at most `Δ` (the
matrices whose off-diagonal nonzero entries join vertices at distance at most `2` in `G`, such
as `Kᵀ K` for a matrix `K` with pattern `G`), with `T = 40 (1062 (Δ + 1)² + 1)`.

As `IsPlane` requires, `G` is connected and has at least one edge. -/
def SquareFastDeterminant : Prop :=
  ∀ (K : Type u) [Field K] (alg : MatMulAlgorithm K),
    (∀ k, 4 * alg.bound (2 ^ k) ≤ alg.bound (2 ^ (k + 1))) → 1 ≤ alg.bound 1 →
    ∀ {ω C : ℝ}, 2 < ω → alg.HasExponent ω C →
    ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (R : Kasteleyn.RotationSystem G),
      R.IsPlane → ∀ {Δ : ℕ}, (∀ v, G.degree v ≤ Δ) →
      ∃ t : SepTree (Fin n), IsDissection (PlanarSeparator.square G) t ∧ t.verts = Finset.univ ∧
        ∀ A : Matrix (Fin n) (Fin n) K,
          (∀ x y, x ≠ y → A x y ≠ 0 → (PlanarSeparator.square G).Adj x y) →
          AllNodes (NodeRegular A) t →
          (ndCounted (PlanarSeparator.square G) alg A t).val.1 = A.det ∧
            ((ndCounted (PlanarSeparator.square G) alg A t).cost.total : ℝ) ≤
              (5 * C * 2 ^ ω + 2 * C + 2) * (40 * (1062 * ((Δ : ℝ) + 1) ^ 2 + 1) +
                40 * (1062 * ((Δ : ℝ) + 1) ^ 2 + 1) + 1) ^ ω /
                (1 - (2 / 3 : ℝ) ^ (ω / 2 - 1)) * (n : ℝ) ^ (ω / 2)

/-- **Fast nested dissection for positive definite matrices on squares of plane graphs of
bounded degree**: as `SquareFastDeterminant`, with no regularity hypothesis, for positive
definite matrices over a field with a partial order and a star structure (`IsOrderedRing`,
`PosMulReflectLT`, `StarRing`; for instance `ℝ`).

As `IsPlane` requires, `G` is connected and has at least one edge. -/
def SquareFastDeterminantPosDef : Prop :=
  ∀ (L : Type u) [Field L] [PartialOrder L] [StarRing L] [IsOrderedRing L] [PosMulReflectLT L]
    (alg : MatMulAlgorithm L),
    (∀ k, 4 * alg.bound (2 ^ k) ≤ alg.bound (2 ^ (k + 1))) → 1 ≤ alg.bound 1 →
    ∀ {ω C : ℝ}, 2 < ω → alg.HasExponent ω C →
    ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (R : Kasteleyn.RotationSystem G),
      R.IsPlane → ∀ {Δ : ℕ}, (∀ v, G.degree v ≤ Δ) →
      ∃ t : SepTree (Fin n), IsDissection (PlanarSeparator.square G) t ∧ t.verts = Finset.univ ∧
        ∀ A : Matrix (Fin n) (Fin n) L,
          (∀ x y, x ≠ y → A x y ≠ 0 → (PlanarSeparator.square G).Adj x y) → A.PosDef →
          (ndCounted (PlanarSeparator.square G) alg A t).val.1 = A.det ∧
            ((ndCounted (PlanarSeparator.square G) alg A t).cost.total : ℝ) ≤
              (5 * C * 2 ^ ω + 2 * C + 2) * (40 * (1062 * ((Δ : ℝ) + 1) ^ 2 + 1) +
                40 * (1062 * ((Δ : ℝ) + 1) ^ 2 + 1) + 1) ^ ω /
                (1 - (2 / 3 : ℝ) ^ (ω / 2 - 1)) * (n : ℝ) ^ (ω / 2)

end Targets

end FastGE

end
