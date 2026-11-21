module

public import FastGE.MatMul
public import NestedDissection.DenseCost
public import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# Block inversion and the determinant with fast matrix multiplication

Recursive block elimination [J. R. Bunch, J. E. Hopcroft, *Triangular factorization and
inversion by fast matrix multiplication*, Math. Comp. 28 (1974), 231–236; A. V. Aho,
J. E. Hopcroft, J. D. Ullman, *The Design and Analysis of Computer Algorithms*, Addison-Wesley
1974, §6.4].  A matrix of size `2 ^ (k + 1)` is split into four blocks of size `2 ^ k`,
```
  M = | A  B |
      | C  D |
```
the leading block `A` is inverted recursively, the Schur complement `S = D - C A⁻¹ B` is formed
with two multiplications and inverted recursively, and
```
  M⁻¹ = | A⁻¹ + A⁻¹ B S⁻¹ C A⁻¹   -A⁻¹ B S⁻¹ |      det M = det A * det S.
        | -S⁻¹ C A⁻¹                S⁻¹       |
```
All products are computed with an arbitrary `MatMulAlgorithm`; six products of size `2 ^ k` are
made at each level.  A scalar inversion is charged one multiplicative operation
(`NestedDissection.opInv`).

The recursion succeeds when every leading block met is invertible; this is the predicate
`Regular k M` (for instance when all leading principal minors are nonzero, see
`FastGE.FastDet`).

## Main definitions

`invDet` is defined in `FastGE/Spec.lean`, `Regular` and `costBound` here.

* `FastGE.BlockInverse.invDet alg k M`: the pair `(M⁻¹, det M)`, in the counting monad.
* `FastGE.BlockInverse.Regular k M`: the leading block and the Schur complement are regular,
  recursively, down to nonzero `1 × 1` pivots.
* `FastGE.BlockInverse.costBound alg k`: the solution of the recurrence
  `c (k + 1) = 2 * c k + 6 * M (2 ^ k) + 4 * 4 ^ k + 1`, `c 0 = 1`, where `M = alg.bound`.

## Main results

* `FastGE.BlockInverse.invDet_val`: `(invDet alg k M).val = (M⁻¹, det M)` when `Regular k M`.
* `FastGE.BlockInverse.invDet_cost_le`: at most `costBound alg k` operations.
* `FastGE.BlockInverse.costBound_add_one_le`: if `4 * M (2 ^ k) ≤ M (2 ^ (k + 1))` for all `k`
  and `1 ≤ M 1`, then `costBound alg k + 1 ≤ 5 * M (2 ^ k)`: inversion and the determinant
  cost no more than a constant times one multiplication.
-/

namespace FastGE

open WordRAM.Algebraic Matrix

@[expose] public section

universe u

namespace BlockInverse

variable {K : Type u}

/-! ### Entrywise negation -/

@[simp] theorem val_matNeg [Neg K] {m n : Type*} [Fintype m] [Fintype n] (A : Matrix m n K) :
    (matNeg A).val = -A := rfl

@[simp] theorem cost_matNeg [Neg K] {m n : Type*} [Fintype m] [Fintype n] (A : Matrix m n K) :
    (matNeg A).cost = ⟨Fintype.card m * Fintype.card n, 0⟩ := by
  ext <;> simp [matNeg, Finset.card_univ]

/-! ### The block inverse formula -/

/-- The block inverse formula, with the leading block and its Schur complement invertible. -/
theorem inv_fromBlocks [Field K] {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] (A : Matrix m m K) (B : Matrix m n K) (C : Matrix n m K) (D : Matrix n n K)
    (hA : A.det ≠ 0) (hS : (D - C * A⁻¹ * B).det ≠ 0) :
    (fromBlocks A B C D)⁻¹ =
      fromBlocks (A⁻¹ + A⁻¹ * B * (D - C * A⁻¹ * B)⁻¹ * C * A⁻¹)
        (-(A⁻¹ * B * (D - C * A⁻¹ * B)⁻¹)) (-((D - C * A⁻¹ * B)⁻¹ * C * A⁻¹))
        (D - C * A⁻¹ * B)⁻¹ := by
  let iA := invertibleOfIsUnitDet A hA.isUnit
  have e : ⅟A = A⁻¹ := invOf_eq_nonsing_inv A
  let iS : Invertible (D - C * ⅟A * B) := invertibleOfIsUnitDet _ (by rw [e]; exact hS.isUnit)
  let := fromBlocks₁₁Invertible A B C D
  rw [← invOf_eq_nonsing_inv, invOf_fromBlocks₁₁_eq]
  simp only [invOf_eq_nonsing_inv]

/-- The determinant of a block matrix with invertible leading block. -/
theorem det_fromBlocks [Field K] {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] (A : Matrix m m K) (B : Matrix m n K) (C : Matrix n m K) (D : Matrix n n K)
    (hA : A.det ≠ 0) :
    (fromBlocks A B C D).det = A.det * (D - C * A⁻¹ * B).det := by
  let := invertibleOfIsUnitDet A hA.isUnit
  rw [det_fromBlocks₁₁, invOf_eq_nonsing_inv]

/-! ### The algorithm -/

theorem eq_idx0 (i : Fin (2 ^ 0)) : i = idx0 :=
  Fin.ext (by have := i.2; simp only [pow_zero] at this; simp [idx0])

instance : Unique (Fin (2 ^ 0)) := ⟨⟨idx0⟩, eq_idx0⟩

variable [Field K]

/-- The recursion of `invDet` meets only invertible leading blocks: the `1 × 1` pivots are
nonzero, and recursively the leading block and its Schur complement are regular. -/
def Regular : (k : ℕ) → SqMat (2 ^ k) K → Prop
  | 0, M => M idx0 idx0 ≠ 0
  | k + 1, M => Regular k (Strassen.split M).toBlocks₁₁ ∧
      Regular k ((Strassen.split M).toBlocks₂₂ -
        (Strassen.split M).toBlocks₂₁ * ((Strassen.split M).toBlocks₁₁)⁻¹ *
          (Strassen.split M).toBlocks₁₂)

theorem det_split {k : ℕ} (M : SqMat (2 ^ (k + 1)) K) : (Strassen.split M).det = M.det :=
  det_reindex_self _ _

theorem inv_split {k : ℕ} (M : SqMat (2 ^ (k + 1)) K) :
    (Strassen.split M)⁻¹ = Strassen.split M⁻¹ :=
  inv_reindex _ _ _

/-- **Correctness of block inversion**: for a regular matrix, `invDet` returns its inverse and
its determinant, and the determinant is nonzero. -/
theorem invDet_val (alg : MatMulAlgorithm K) :
    ∀ (k : ℕ) (M : SqMat (2 ^ k) K), Regular k M →
      (invDet alg k M).val = (M⁻¹, M.det) ∧ M.det ≠ 0
  | 0, M, h => by
    have hdet : M.det = M idx0 idx0 := det_unique M
    refine ⟨?_, hdet ▸ h⟩
    simp only [invDet, Counted.val_bind, NestedDissection.val_opInv, Counted.val_pure,
      hdet, Prod.mk.injEq, and_true]
    refine (inv_eq_left_inv ?_).symm
    ext i j
    rw [eq_idx0 i, eq_idx0 j]
    simp only [Matrix.mul_apply, Finset.univ_unique, Finset.sum_singleton, of_apply, one_apply_eq]
    exact inv_mul_cancel₀ h
  | k + 1, M, h => by
    obtain ⟨h₁, h₂⟩ := h
    set A := (Strassen.split M).toBlocks₁₁
    set B := (Strassen.split M).toBlocks₁₂
    set C := (Strassen.split M).toBlocks₂₁
    set D := (Strassen.split M).toBlocks₂₂
    obtain ⟨hv₁, hA⟩ := invDet_val alg k A h₁
    obtain ⟨hv₂, hS⟩ := invDet_val alg k (D - C * A⁻¹ * B) h₂
    have hM : Strassen.split M = fromBlocks A B C D := (fromBlocks_toBlocks _).symm
    have hdet : M.det = A.det * (D - C * A⁻¹ * B).det := by
      rw [← det_split, hM, det_fromBlocks _ _ _ _ hA]
    refine ⟨?_, hdet ▸ mul_ne_zero hA hS⟩
    simp only [invDet, Counted.val_bind, Counted.val_pure, Mat.val_sub, Mat.val_add,
      val_matNeg, Op.val_mul, alg.mul_val]
    rw [hv₁]
    simp only
    rw [hv₂]
    simp only [Prod.mk.injEq, hdet, and_true]
    rw [Strassen.join_eq_iff, ← inv_split, hM, inv_fromBlocks _ _ _ _ hA hS]
    simp only [Matrix.mul_assoc, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₁]

/-! ### Operation count -/

/-- The bound on the number of operations of `invDet alg k`: the solution of
`c (k + 1) = 2 * c k + 6 * M (2 ^ k) + 4 * 4 ^ k + 1`, `c 0 = 1`, with `M = alg.bound`. -/
def costBound (alg : MatMulAlgorithm K) : ℕ → ℕ
  | 0 => 1
  | k + 1 => 2 * costBound alg k + 6 * alg.bound (2 ^ k) + 4 * (2 ^ k * 2 ^ k) + 1

/-- **Operation count of block inversion.** -/
theorem invDet_cost_le (alg : MatMulAlgorithm K) :
    ∀ (k : ℕ) (M : SqMat (2 ^ k) K), (invDet alg k M).cost.total ≤ costBound alg k
  | 0, M => by simp [invDet, costBound, OpCount.total]
  | k + 1, M => by
    simp only [invDet, Counted.cost_bind, Counted.cost_pure, OpCount.total_add,
      Mat.cost_sub, Mat.cost_add, cost_matNeg, Op.cost_mul, Fintype.card_fin,
      OpCount.total_mk, OpCount.total_zero, costBound]
    have hc : ∀ N, (invDet alg k N).cost.total ≤ costBound alg k := invDet_cost_le alg k
    have hm : ∀ X Y, (alg.mul (2 ^ k) X Y).cost.total ≤ alg.bound (2 ^ k) := alg.cost_le _
    grw [hc, hc, hm, hm, hm, hm, hm, hm]
    omega

/-- Under the regularity condition `4 * M (2 ^ k) ≤ M (2 ^ (k + 1))` and `1 ≤ M 1`, the
multiplication bound is at least quadratic on powers of two. -/
theorem sq_le_bound (alg : MatMulAlgorithm K)
    (hreg : ∀ k, 4 * alg.bound (2 ^ k) ≤ alg.bound (2 ^ (k + 1))) (h1 : 1 ≤ alg.bound 1) :
    ∀ k, 2 ^ k * 2 ^ k ≤ alg.bound (2 ^ k)
  | 0 => by simpa using h1
  | k + 1 => by
    have := sq_le_bound alg hreg h1 k
    have := hreg k
    have e : 2 ^ (k + 1) * 2 ^ (k + 1) = 4 * (2 ^ k * 2 ^ k) := by ring
    omega

/-- **Block inversion costs `O(M(n))`.**  If the multiplication bound `M = alg.bound` satisfies
`4 * M (2 ^ k) ≤ M (2 ^ (k + 1))` and `1 ≤ M 1`, then inverting a matrix of size `2 ^ k` and
computing its determinant costs at most `5 * M (2 ^ k) - 1` operations. -/
theorem costBound_add_one_le (alg : MatMulAlgorithm K)
    (hreg : ∀ k, 4 * alg.bound (2 ^ k) ≤ alg.bound (2 ^ (k + 1))) (h1 : 1 ≤ alg.bound 1) :
    ∀ k, costBound alg k + 1 ≤ 5 * alg.bound (2 ^ k)
  | 0 => by simp only [costBound, pow_zero]; omega
  | k + 1 => by
    have := costBound_add_one_le alg hreg h1 k
    have := hreg k
    have := sq_le_bound alg hreg h1 (k + 1)
    have e : 2 ^ (k + 1) * 2 ^ (k + 1) = 4 * (2 ^ k * 2 ^ k) := by ring
    simp only [costBound]
    omega

theorem invDet_cost_le_bound (alg : MatMulAlgorithm K)
    (hreg : ∀ k, 4 * alg.bound (2 ^ k) ≤ alg.bound (2 ^ (k + 1))) (h1 : 1 ≤ alg.bound 1)
    (k : ℕ) (M : SqMat (2 ^ k) K) : (invDet alg k M).cost.total + 1 ≤ 5 * alg.bound (2 ^ k) :=
  le_trans (Nat.add_le_add_right (invDet_cost_le alg k M) 1) (costBound_add_one_le alg hreg h1 k)

end BlockInverse

end

end FastGE
