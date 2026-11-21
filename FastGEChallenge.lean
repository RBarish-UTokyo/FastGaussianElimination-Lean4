module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.GroupTheory.Perm.Cycle.Factors
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Fintype.Perm
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Data.Matrix.Block
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Data.Nat.Log
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Data.Matrix.ColumnRowPartitioned

/-!
# Challenge: fast matrix multiplication, inversion, and nested dissection

This file is the statement a mathematical reader should audit. Costs are counted operations in
the arithmetic model: algorithms are written in the monad `WordRAM.Algebraic.Counted`, and the
cost of a computation is the number of ring operations performed through its charged
primitives. It states:

* `FastGE.strassen_count`: Strassen's algorithm on matrices of size `2 ^ k` computes the product
  with exactly `7 ^ k` multiplications and `6 (7 ^ k - 4 ^ k)` additive operations;
* `FastGE.strassen_exponent`: padded to the next power of two, it is a multiplication algorithm of
  exponent `ω₀ = log₂ 7` (at most `49 n ^ ω₀` operations), and `2 < ω₀ < 3`;
* `FastGE.inverse_determinant`: for every multiplication algorithm whose bound `M` satisfies
  `4 M (2 ^ k) ≤ M (2 ^ (k + 1))` and `1 ≤ M 1`, block inversion computes the inverse and the
  determinant of a matrix with nonzero leading principal minors, in fewer than
  `5 M (2 ^ ⌈log₂ n⌉)` operations;
* `FastGE.planar_fast_determinant`, `FastGE.square_fast_determinant`,
  `FastGE.square_fast_determinant_posDef`: for a multiplication algorithm of exponent `ω > 2` whose
  bound satisfies the same two conditions, and a plane graph (or the square of a plane graph of
  bounded degree), block elimination along a suitable separator tree computes the determinant of
  every matrix with that pattern for which the elimination meets only invertible blocks
  (`NodeRegular` at every node), or, in the square case, of every positive definite matrix with that
  pattern, in `O(n ^ (ω / 2))` operations. Plane graphs are connected and have at least one edge
  (`IsPlane`); the disconnected case is not formalized.

Strassen's algorithm, its exponent, and inversion with the determinant by recursive block
elimination for matrices with nonzero leading principal minors are from

  V. Strassen, *Gaussian elimination is not optimal*, Numer. Math. 13 (1969), 354-356;

the bound `O(M(n))` in terms of an arbitrary multiplication algorithm follows

  J. R. Bunch, J. E. Hopcroft, *Triangular factorization and inversion by fast matrix
  multiplication*, Math. Comp. 28 (1974), 231-236,

whose pivoting for general invertible matrices is not formalized. Nested dissection with fast
matrix multiplication on plane graphs, in `O(n ^ (ω / 2))` operations, is from

  R. J. Lipton, D. J. Rose, R. E. Tarjan, *Generalized nested dissection*, SIAM J. Numer. Anal.
  16 (1979), 346-358;
  V. Pan, J. Reif, *Fast and efficient parallel solution of sparse linear systems*, SIAM J.
  Comput. 22 (1993), 1227-1250.

The explicit constants are those of this formalization. The case of squares of plane graphs of
bounded degree, and of positive definite matrices without the regularity hypothesis, are derived
here from those results: the square has separator trees obtained from separators of closed
neighbourhoods, and the principal minors of a positive definite matrix are positive.

The authoritative sources of every definition below are the specification modules
`WordRAM/AlgebraicSpec.lean`, `Kasteleyn/Spec.lean` (section `Map`), `NestedDissection/Spec.lean`
and `FastGE/Spec.lean`, which the proofs import. This file is their self-contained copy, followed
by the six targets with `sorry`. The comparator checks that every constant used by the six
statements is the same kernel constant (type and value) in the solution's environment.
-/
@[expose] public section

namespace WordRAM.Algebraic

/-! ### Operation counts -/

/-- A count of arithmetic operations: `adds` counts additions, subtractions and negations,
`muls` counts multiplications. -/
structure OpCount where
  /-- Number of additive operations (additions, subtractions, negations). -/
  adds : ℕ
  /-- Number of multiplications. -/
  muls : ℕ

namespace OpCount

instance : Zero OpCount := ⟨⟨0, 0⟩⟩

instance : Add OpCount := ⟨fun a b => ⟨a.adds + b.adds, a.muls + b.muls⟩⟩

instance : AddCommMonoid OpCount where
  add_assoc a b c :=
    congrArg₂ OpCount.mk (Nat.add_assoc a.adds b.adds c.adds) (Nat.add_assoc a.muls b.muls c.muls)
  zero_add a := congrArg₂ OpCount.mk (Nat.zero_add a.adds) (Nat.zero_add a.muls)
  add_zero a := congrArg₂ OpCount.mk (Nat.add_zero a.adds) (Nat.add_zero a.muls)
  add_comm a b := congrArg₂ OpCount.mk (Nat.add_comm a.adds b.adds) (Nat.add_comm a.muls b.muls)
  nsmul := nsmulRec

/-- Total number of arithmetic operations. -/
def total (c : OpCount) : ℕ := c.adds + c.muls

/-- One additive operation. -/
abbrev oneAdd : OpCount := ⟨1, 0⟩

/-- One multiplication. -/
abbrev oneMul : OpCount := ⟨0, 1⟩

end OpCount

/-! ### The counting monad -/

universe u v

/-- A computation in the arithmetic cost model: a result `val` together with the number of
ring operations `cost` performed to obtain it (the writer monad over `OpCount`). -/
structure Counted (α : Type u) where
  /-- The computed value. -/
  val : α
  /-- The number of operations spent. -/
  cost : OpCount

namespace Counted

instance : Monad Counted where
  pure a := ⟨a, 0⟩
  bind x f := ⟨(f x.val).val, x.cost + (f x.val).cost⟩

/-- Run a family of independent counted computations indexed by a finite type: the value is
the family of values, the cost is the sum of the costs. -/
def pi {ι : Type v} [Fintype ι] {α : ι → Type u} (f : (i : ι) → Counted (α i)) :
    Counted ((i : ι) → α i) :=
  ⟨fun i => (f i).val, ∑ i, (f i).cost⟩

end Counted

/-! ### Primitive ring operations -/

namespace Op

variable {R : Type u}

/-- Addition, charged one additive operation. -/
def add [Add R] (a b : R) : Counted R := ⟨a + b, OpCount.oneAdd⟩

/-- Subtraction, charged one additive operation. -/
def sub [Sub R] (a b : R) : Counted R := ⟨a - b, OpCount.oneAdd⟩

/-- Negation, charged one additive operation. -/
def neg [Neg R] (a : R) : Counted R := ⟨-a, OpCount.oneAdd⟩

/-- Multiplication, charged one multiplication. -/
def mul [Mul R] (a b : R) : Counted R := ⟨a * b, OpCount.oneMul⟩

end Op

/-! ### Entrywise matrix operations -/

/-- Square matrices of size `n` over `R`. -/
abbrev SqMat (n : ℕ) (R : Type u) : Type u := Matrix (Fin n) (Fin n) R

namespace Mat

variable {R : Type u} {m : Type v} {n : Type v} [Fintype m] [Fintype n]

/-- Entrywise matrix addition, one additive operation per entry. -/
def add [Add R] (A B : Matrix m n R) : Counted (Matrix m n R) :=
  Counted.pi fun i => Counted.pi fun j => Op.add (A i j) (B i j)

/-- Entrywise matrix subtraction, one additive operation per entry. -/
def sub [Sub R] (A B : Matrix m n R) : Counted (Matrix m n R) :=
  Counted.pi fun i => Counted.pi fun j => Op.sub (A i j) (B i j)

end Mat

end WordRAM.Algebraic

end

@[expose] public section

namespace Kasteleyn

open Finset SimpleGraph

/-! ### Rotation systems and faces -/

section Map

variable {V : Type*} {G : SimpleGraph V}

/-- A rotation system on a simple graph `G`: a permutation `rot` of the darts of `G` which,
for every vertex `v`, permutes the darts leaving `v` in a single cycle. -/
structure RotationSystem (G : SimpleGraph V) where
  /-- The successor of a dart in the cyclic order of the darts leaving its initial vertex. -/
  rot : Equiv.Perm G.Dart
  fst_rot : ∀ d, (rot d).fst = d.fst
  sameCycle_of_fst_eq : ∀ d d' : G.Dart, d.fst = d'.fst → rot.SameCycle d d'

/-- The reversal of darts as a permutation. -/
def dartRev (G : SimpleGraph V) : Equiv.Perm G.Dart :=
  Function.Involutive.toPerm _ Dart.symm_involutive

namespace RotationSystem

variable (M : RotationSystem G)

/-- The face permutation: the boundary walk of a face continues a dart `d` by the successor of
`d.symm` in the rotation at the head of `d`. -/
def faceNext : Equiv.Perm G.Dart := (dartRev G).trans M.rot

/-- The faces: the cycles of the face permutation. -/
def Face : Type _ := Quotient (Equiv.Perm.SameCycle.setoid M.faceNext)

/-- The face of a dart: the face whose boundary walk traverses the dart. -/
def face (d : G.Dart) : M.Face := Quotient.mk _ d

section Fintype

variable [Fintype V] [DecidableRel G.Adj]

variable [DecidableEq V]

instance : DecidableEq M.Face :=
  @Quotient.decidableEq _ _ (Equiv.Perm.instDecidableRelSameCycle M.faceNext)

instance : Fintype M.Face :=
  @Quotient.fintype _ _ _ (Equiv.Perm.instDecidableRelSameCycle M.faceNext)

/-- A rotation system is *plane* (of genus zero) if the graph is connected and Euler's formula
`V - E + F = 2` holds.

Faces are the cycles of the face permutation on the darts, so a graph without edges has no
faces here. A connected graph without edges is a single vertex; it is not plane in this sense
(`1 + 0 ≠ 0 + 2`), so statements assuming `IsPlane` leave it out. -/
structure IsPlane : Prop where
  connected : G.Connected
  euler : Fintype.card V + Fintype.card M.Face = #G.edgeFinset + 2

end Fintype

end RotationSystem

end Map

end Kasteleyn

end

@[expose] public section

namespace NestedDissection

universe u v w

/-! ### Separator trees -/

/-- A separator tree: a leaf holding a vertex set, or a node holding a separator and two
subtrees for the two parts. -/
inductive SepTree (V : Type u) : Type u
  | leaf (s : Finset V) : SepTree V
  | node (s : Finset V) (a b : SepTree V) : SepTree V

section Bdry

variable {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The boundary of `W`: the vertices outside `W` adjacent to a vertex of `W`. -/
def bdry (W : Finset V) : Finset V := {y | y ∉ W ∧ ∃ x ∈ W, G.Adj x y}

end Bdry

namespace SepTree

variable {V : Type u}

/-- The vertices numbered at the root of a subtree: the separator of a node, the whole set of a
leaf. -/
def own : SepTree V → Finset V
  | leaf s => s
  | node s _ _ => s

/-- `P` holds at every node of the tree. -/
def AllNodes (P : SepTree V → Prop) : SepTree V → Prop
  | leaf s => P (leaf s)
  | node s a b => P (node s a b) ∧ AllNodes P a ∧ AllNodes P b

variable [DecidableEq V]

/-- All vertices of a subtree. -/
def verts : SepTree V → Finset V
  | leaf s => s
  | node s a b => s ∪ a.verts ∪ b.verts

/-- `t` is a separator tree of `G`: at every node the separator and the two parts are pairwise
disjoint and no edge of `G` joins the two parts. -/
def IsDissection (G : SimpleGraph V) : SepTree V → Prop
  | leaf _ => True
  | node s a b => Disjoint s a.verts ∧ Disjoint s b.verts ∧ Disjoint a.verts b.verts ∧
      (∀ x ∈ a.verts, ∀ y ∈ b.verts, ¬ G.Adj x y) ∧ IsDissection G a ∧ IsDissection G b

/-- The parts of the root have at most two thirds of its vertices. -/
def Shrinks : SepTree V → Prop
  | leaf _ => True
  | node s a b => 3 * a.verts.card ≤ 2 * (node s a b).verts.card ∧
      3 * b.verts.card ≤ 2 * (node s a b).verts.card

/-- The separator bound `|own t| ≤ α √k` and the boundary bound `|bdry t| ≤ β √k` at the root
of `t`, where `k` is the number of vertices of `t`. -/
def SqrtBound [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (α β : ℝ) (t : SepTree V) :
    Prop :=
  (t.own.card : ℝ) ≤ α * √(t.verts.card) ∧ ((bdry G t.verts).card : ℝ) ≤ β * √(t.verts.card)

section Order

variable [LinearOrder V]

/-- The nested dissection order: recursively the first part, the second part, then the
separator (each separator and leaf set in increasing order of `V`). -/
def order : SepTree V → List V
  | leaf s => s.sort (· ≤ ·)
  | node s a b => order a ++ order b ++ s.sort (· ≤ ·)

end Order

end SepTree

/-! ### The filled graph -/

section Fill

variable {V : Type u} (G : SimpleGraph V) (r : V → ℕ)

/-- `LowWalk G r k u w`: there is a walk of positive length from `u` to `w` in `G` all of whose
interior vertices have rank `< k`. -/
inductive LowWalk (k : ℕ) : V → V → Prop
  | adj {u w : V} : G.Adj u w → LowWalk k u w
  | cons {u x w : V} : G.Adj u x → r x < k → LowWalk k x w → LowWalk k u w

namespace LowWalk

variable {G r} {k : ℕ} {u w : V}

theorem trans {x : V} (h₁ : LowWalk G r k u x) (hx : r x < k) (h₂ : LowWalk G r k x w) :
    LowWalk G r k u w := by
  induction h₁ with
  | adj h => exact .cons h hx h₂
  | cons h hy _ ih => exact .cons h hy (ih hx h₂)

theorem symm (h : LowWalk G r k u w) : LowWalk G r k w u := by
  induction h with
  | adj h => exact .adj h.symm
  | cons h hx _ ih => exact ih.trans hx (.adj h.symm)

end LowWalk

/-- The **filled graph** of `G` for the elimination order given by `r`: `u ≠ w` are adjacent
iff there is a walk from `u` to `w` whose interior vertices all have rank smaller than both
`r u` and `r w`. -/
def fill : SimpleGraph V where
  Adj u w := u ≠ w ∧ LowWalk G r (min (r u) (r w)) u w
  symm := ⟨fun u w h => ⟨h.1.symm, by rw [min_comm]; exact h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

variable {G r}

variable (r) in
/-- The neighbours of `v` in `H` that come later in the order `r`. -/
def laterNbrs [Fintype V] (H : SimpleGraph V) [DecidableRel H.Adj] (v : V) : Finset V :=
  {w | H.Adj v w ∧ r v < r w}

end Fill

/-! ### Elimination -/

section Elimination

open WordRAM.Algebraic Matrix

variable {K : Type u}

/-- Inversion, charged one multiplicative operation (the cost model `OpCount` records additive
and multiplicative operations; a division or inversion is counted with the latter). -/
def opInv [Inv K] (a : K) : Counted K := ⟨a⁻¹, OpCount.oneMul⟩

/-- The leading principal `k × k` submatrix. -/
def leading {n : ℕ} (A : Matrix (Fin n) (Fin n) K) (k : ℕ) (hk : k ≤ n) :
    Matrix (Fin k) (Fin k) K :=
  A.submatrix (Fin.castLE hk) (Fin.castLE hk)

variable [Field K]

/-- The in-place elimination step with pivot `k`: `M i j - M i k * (M k k)⁻¹ * M k j` for
`i, j > k`. The inverse is the field's, with `0⁻¹ = 0`, so at a zero pivot the step leaves `M`
unchanged. -/
def elimStep {n : ℕ} (k : Fin n) (M : Matrix (Fin n) (Fin n) K) : Matrix (Fin n) (Fin n) K :=
  Matrix.of fun i j => if k < i ∧ k < j then M i j - M i k * (M k k)⁻¹ * M k j else M i j

/-- `stage A k`: the matrix after the elimination steps with pivots `0, …, k - 1`; Gaussian
elimination without pivoting when these pivots are nonzero. -/
def stage {n : ℕ} (A : Matrix (Fin n) (Fin n) K) : ℕ → Matrix (Fin n) (Fin n) K
  | 0 => A
  | k + 1 => if h : k < n then elimStep ⟨k, h⟩ (stage A k) else stage A k

variable {n : ℕ} (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]

/-- The elimination step with pivot `k` restricted to the positions `(i, j)` with `i` and `j`
later neighbours of `k` in `H`, in the counting monad: one inversion, one multiplication for
each multiplier, one multiplication and one subtraction for each updated entry. -/
def sparseStepCounted (k : Fin n) (M : Matrix (Fin n) (Fin n) K) :
    Counted (Matrix (Fin n) (Fin n) K) := do
  let p ← opInv (M k k)
  let l ← Counted.pi fun i : Fin n =>
    if i ∈ laterNbrs Fin.val H k then Op.mul (M i k) p else pure 0
  let S ← Counted.pi fun i : Fin n => Counted.pi fun j : Fin n =>
    if i ∈ laterNbrs Fin.val H k ∧ j ∈ laterNbrs Fin.val H k then do
      let t ← Op.mul (l i) (M k j)
      Op.sub (M i j) t
    else pure (M i j)
  pure (Matrix.of S)

/-- Restricted elimination in the counting monad: the first `k` steps. -/
def sparseCounted (A : Matrix (Fin n) (Fin n) K) : ℕ → Counted (Matrix (Fin n) (Fin n) K)
  | 0 => pure A
  | k + 1 => do
    let M ← sparseCounted A k
    if h : k < n then sparseStepCounted H ⟨k, h⟩ M else pure M

end Elimination

end NestedDissection

/-! ### Squares of graphs -/

namespace PlanarSeparator

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

variable (G) in
/-- The square of a graph: distinct vertices at distance at most `2` are adjacent. -/
def square : SimpleGraph V where
  Adj i j := i ≠ j ∧ (G.Adj i j ∨ ∃ k, G.Adj i k ∧ G.Adj k j)
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.elim (fun h => Or.inl h.symm)
    fun ⟨k, h1, h2⟩ => Or.inr ⟨k, h2.symm, h1.symm⟩⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

instance : DecidableRel (square G).Adj := fun _ _ =>
  inferInstanceAs (Decidable (_ ∧ _))

end PlanarSeparator

end

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

/-! ## The targets -/

public section

namespace FastGE

universe u

/-- **Strassen's algorithm and its exact operation count.** -/
theorem strassen_count : StrassenCount.{u} := by
  sorry

/-- **The exponent of Strassen's algorithm.** -/
theorem strassen_exponent : StrassenExponent.{u} := by
  sorry

/-- **Inverse and determinant in `O(M(n))` operations.** -/
theorem inverse_determinant : InverseDeterminant.{u} := by
  sorry

/-- **Fast nested dissection for plane graphs.** -/
theorem planar_fast_determinant : PlanarFastDeterminant.{u} := by
  sorry

/-- **Fast nested dissection for squares of plane graphs of bounded degree.** -/
theorem square_fast_determinant : SquareFastDeterminant.{u} := by
  sorry

/-- **Fast nested dissection for positive definite matrices on squares of plane graphs of bounded
degree.** -/
theorem square_fast_determinant_posDef : SquareFastDeterminantPosDef.{u} := by
  sorry

end FastGE

end
