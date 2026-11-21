module

public import FastGE.BlockInverse
public import NestedDissection.PosDef

/-!
# Inverse and determinant in `O(M(n))` operations

For a square matrix `A` over a field whose leading principal minors are all nonzero, block
inversion (`FastGE.BlockInverse`) computes `A⁻¹` and `det A` with a constant number of matrix
multiplications per level of the recursion [J. R. Bunch, J. E. Hopcroft, *Triangular
factorization and inversion by fast matrix multiplication*, Math. Comp. 28 (1974), 231–236;
A. V. Aho, J. E. Hopcroft, J. D. Ullman, *The Design and Analysis of Computer Algorithms*,
Addison-Wesley 1974, §6.4].

An `n × n` matrix `A` is first embedded as the leading block of the `N × N` matrix
`padOne A = diag(A, 1)`, where `N = 2 ^ ⌈log₂ n⌉`.  The leading principal minors of `padOne A`
are those of `A` followed by copies of `det A`, so they are all nonzero again
(`leading_padOne_ne_zero`).

The leading principal minors of a matrix past a leading block `P` are `det P` times the
leading principal minors of the Schur complement of `P` (`det_leading_add`); hence nonzero
leading principal minors make the block recursion succeed (`regular_of_leading`).

## Main definitions

These definitions are in `FastGE/Spec.lean`.

* `FastGE.FastDet.padOne h A`: the matrix `diag(A, 1)` of size `N ≥ n`.
* `FastGE.FastDet.invDet alg A`: the pair `(A⁻¹, det A)` computed by block inversion of
  `padOne A`, with all products computed by the multiplication algorithm `alg`.

## Main results

* `FastGE.FastDet.invDet_val`: `(invDet alg A).val = (A⁻¹, det A)` when all leading principal
  minors of `A` are nonzero.
* `FastGE.FastDet.invDet_val_of_posDef`: the same for positive definite matrices.
* `FastGE.FastDet.invDet_cost_le_bound`: if the multiplication bound `M` satisfies
  `4 * M (2 ^ k) ≤ M (2 ^ (k + 1))` and `1 ≤ M 1`, then
  `cost + 1 ≤ 5 * M (2 ^ ⌈log₂ n⌉)`.
* `FastGE.FastDet.invDet_cost_le_rpow`: if moreover `alg` has exponent `ω` with constant `C`,
  then `cost ≤ 5 * C * 2 ^ ω * n ^ ω`.
* `FastGE.FastDet.invDet_strassen_cost_le`: with Strassen's algorithm,
  `cost ≤ 245 * n ^ log₂ 7`.
-/

namespace FastGE

open WordRAM.Algebraic Matrix NestedDissection

@[expose] public section

universe u

namespace FastDet

variable {K : Type u}

/-! ### Leading principal minors of block matrices -/

section Leading

/-- The leading principal submatrices of the leading block are leading principal submatrices
of the whole matrix. -/
theorem leading_toBlocks₁₁ {N m p : ℕ} (e : Fin N ≃ Fin m ⊕ Fin p)
    (he : ∀ i, (e.symm (Sum.inl i) : ℕ) = i) (A : Matrix (Fin N) (Fin N) K) (j : ℕ)
    (hj : j ≤ m) (hjN : j ≤ N) :
    leading (reindex e e A).toBlocks₁₁ j hj = leading A j hjN := by
  ext a b
  simp only [leading, submatrix_apply, toBlocks₁₁, reindex_apply, of_apply]
  congr 1 <;> exact Fin.ext (by simp [he])

/-- A leading principal submatrix containing the leading block, as a block matrix. -/
theorem leading_add_eq_fromBlocks {N m p : ℕ} (e : Fin N ≃ Fin m ⊕ Fin p)
    (he₁ : ∀ i, (e.symm (Sum.inl i) : ℕ) = i) (he₂ : ∀ i, (e.symm (Sum.inr i) : ℕ) = m + i)
    (A : Matrix (Fin N) (Fin N) K) (j : ℕ) (hj : j ≤ p) (hjN : m + j ≤ N) :
    (leading A (m + j) hjN).submatrix finSumFinEquiv finSumFinEquiv =
      fromBlocks (reindex e e A).toBlocks₁₁
        ((reindex e e A).toBlocks₁₂.submatrix id (Fin.castLE hj))
        ((reindex e e A).toBlocks₂₁.submatrix (Fin.castLE hj) id)
        (leading (reindex e e A).toBlocks₂₂ j hj) := by
  ext (a | a) (b | b) <;>
  · simp only [leading, submatrix_apply, toBlocks₁₁, toBlocks₁₂, toBlocks₂₁, toBlocks₂₂,
      reindex_apply, of_apply, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁,
      fromBlocks_apply₂₂, id]
    congr 1 <;> exact Fin.ext (by simp [he₁, he₂])

variable [Field K]

/-- **Leading minors and the Schur complement.**  If the leading block `P` of size `m` is
invertible, the leading principal minor of order `m + j` is `det P` times the leading principal
minor of order `j` of the Schur complement `D - C P⁻¹ B`. -/
theorem det_leading_add {N m p : ℕ} (e : Fin N ≃ Fin m ⊕ Fin p)
    (he₁ : ∀ i, (e.symm (Sum.inl i) : ℕ) = i) (he₂ : ∀ i, (e.symm (Sum.inr i) : ℕ) = m + i)
    (A : Matrix (Fin N) (Fin N) K) (hP : (reindex e e A).toBlocks₁₁.det ≠ 0)
    (j : ℕ) (hj : j ≤ p) (hjN : m + j ≤ N) :
    (leading A (m + j) hjN).det = (reindex e e A).toBlocks₁₁.det *
      (leading ((reindex e e A).toBlocks₂₂ - (reindex e e A).toBlocks₂₁ *
        ((reindex e e A).toBlocks₁₁)⁻¹ * (reindex e e A).toBlocks₁₂) j hj).det := by
  rw [← det_submatrix_equiv_self finSumFinEquiv, leading_add_eq_fromBlocks e he₁ he₂ A j hj hjN,
    BlockInverse.det_fromBlocks _ _ _ _ hP]
  congr 2

end Leading

/-! ### Nonzero leading minors make the block recursion succeed -/

theorem halves_symm_inl (k : ℕ) (i : Fin (2 ^ k)) :
    ((Strassen.halves k).symm (Sum.inl i) : ℕ) = i := by
  simp [Strassen.halves]

theorem halves_symm_inr (k : ℕ) (i : Fin (2 ^ k)) :
    ((Strassen.halves k).symm (Sum.inr i) : ℕ) = 2 ^ k + i := by
  simp [Strassen.halves, add_comm]

variable [Field K]

/-- If all leading principal minors of a matrix of size `2 ^ k` are nonzero, block inversion
meets only invertible leading blocks. -/
theorem regular_of_leading : ∀ (k : ℕ) (M : SqMat (2 ^ k) K),
    (∀ j hj, (leading M j hj).det ≠ 0) → BlockInverse.Regular k M
  | 0, M, h => by
    have := h 1 (by simp)
    rw [det_fin_one] at this
    exact this
  | k + 1, M, h => by
    have hle : 2 ^ k ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right two_pos (Nat.le_succ k)
    have h₁ : ∀ j hj, (leading (Strassen.split M).toBlocks₁₁ j hj).det ≠ 0 := fun j hj => by
      rw [Strassen.split, leading_toBlocks₁₁ _ (halves_symm_inl k) M j hj (hj.trans hle)]
      exact h _ _
    have hA : (Strassen.split M).toBlocks₁₁.det ≠ 0 := by simpa using h₁ (2 ^ k) le_rfl
    refine ⟨regular_of_leading k _ h₁, regular_of_leading k _ fun j hj => ?_⟩
    have hjN : 2 ^ k + j ≤ 2 ^ (k + 1) := by rw [pow_succ]; omega
    have := h _ hjN
    rw [det_leading_add _ (halves_symm_inl k) (halves_symm_inr k) M hA j hj hjN] at this
    exact right_ne_zero_of_mul this

/-! ### Padding with an identity block -/

section Pad

variable {n N : ℕ}

theorem pad_symm_inl (h : n ≤ N) (i : Fin n) : ((Pad.equiv h).symm (Sum.inl i) : ℕ) = i := by
  simp [Pad.equiv]

theorem pad_symm_inr (h : n ≤ N) (i : Fin (N - n)) :
    ((Pad.equiv h).symm (Sum.inr i) : ℕ) = n + i := by
  simp [Pad.equiv]

theorem reindex_padOne (h : n ≤ N) (A : SqMat n K) :
    reindex (Pad.equiv h) (Pad.equiv h) (padOne h A) = fromBlocks A 0 0 1 := by
  simp [padOne]

@[simp] theorem det_padOne (h : n ≤ N) (A : SqMat n K) : (padOne h A).det = A.det := by
  rw [← det_reindex_self (Pad.equiv h), reindex_padOne, det_fromBlocks_zero₁₂, det_one, mul_one]

theorem inv_padOne (h : n ≤ N) (A : SqMat n K) (hA : A.det ≠ 0) :
    (padOne h A)⁻¹ = padOne h A⁻¹ := by
  refine inv_eq_left_inv ?_
  simp only [padOne, reindex_symm, reindex_apply, submatrix_mul_equiv, fromBlocks_multiply,
    nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hA)]
  simp

@[simp] theorem unpad_padOne (h : n ≤ N) (A : SqMat n K) : Pad.unpad h (padOne h A) = A := by
  simp [padOne, Pad.unpad]

theorem leading_padOne_of_le (h : n ≤ N) (A : SqMat n K) (j : ℕ) (hj : j ≤ n) :
    leading (padOne h A) j (hj.trans h) = leading A j hj := by
  rw [← leading_toBlocks₁₁ _ (pad_symm_inl h) _ j hj, reindex_padOne, toBlocks_fromBlocks₁₁]

/-- Padding with an identity block keeps all leading principal minors nonzero. -/
theorem leading_padOne_ne_zero (h : n ≤ N) (A : SqMat n K)
    (hA : ∀ j hj, (leading A j hj).det ≠ 0) (j : ℕ) (hj : j ≤ N) :
    (leading (padOne h A) j hj).det ≠ 0 := by
  rcases le_or_gt j n with hjn | hjn
  · rw [leading_padOne_of_le h A j hjn]
    exact hA j hjn
  · obtain ⟨p, rfl⟩ := Nat.exists_eq_add_of_le hjn.le
    have hP : (reindex (Pad.equiv h) (Pad.equiv h) (padOne h A)).toBlocks₁₁.det ≠ 0 := by
      rw [reindex_padOne, toBlocks_fromBlocks₁₁]
      simpa using hA n le_rfl
    rw [det_leading_add _ (pad_symm_inl h) (pad_symm_inr h) _ hP p (by omega) hj]
    refine mul_ne_zero hP ?_
    simp only [reindex_padOne, toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂,
      toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂, Matrix.zero_mul, Matrix.mul_zero, sub_zero,
      leading, submatrix_one _ (Fin.castLE_injective _), det_one]
    exact one_ne_zero

theorem two_pow_clog_le (n : ℕ) (hn : 1 ≤ n) : 2 ^ Nat.clog 2 n ≤ 2 * n := by
  rcases Nat.eq_or_lt_of_le hn with rfl | hn
  · simp
  have hk : 0 < Nat.clog 2 n := Nat.clog_pos one_lt_two hn
  have hlt := Nat.pow_pred_clog_lt_self one_lt_two hn
  obtain ⟨m, hm⟩ : ∃ m, Nat.clog 2 n = m + 1 := ⟨Nat.clog 2 n - 1, by omega⟩
  rw [hm, Nat.pred_eq_sub_one, Nat.add_sub_cancel] at hlt
  rw [hm, pow_succ]
  omega

end Pad

/-! ### The algorithm -/

/-- **Correctness**: if all leading principal minors of `A` are nonzero, `invDet` returns `A⁻¹`
and `det A`. -/
theorem invDet_val (alg : MatMulAlgorithm K) {n : ℕ} (A : SqMat n K)
    (hA : ∀ j hj, (leading A j hj).det ≠ 0) : (invDet alg A).val = (A⁻¹, A.det) := by
  have h := Strassen.le_two_pow_clog n
  obtain ⟨hv, -⟩ := BlockInverse.invDet_val alg _ _
    (regular_of_leading _ _ (leading_padOne_ne_zero h A hA))
  have hdet : A.det ≠ 0 := by simpa using hA n le_rfl
  simp only [invDet, Counted.val_map, hv, inv_padOne h A hdet, unpad_padOne, det_padOne]

/-- The determinant of a matrix with nonzero leading principal minors. -/
theorem invDet_val_det (alg : MatMulAlgorithm K) {n : ℕ} (A : SqMat n K)
    (hA : ∀ j hj, (leading A j hj).det ≠ 0) : (invDet alg A).val.2 = A.det := by
  rw [invDet_val alg A hA]

/-- Positive definite matrices have nonzero leading principal minors, so `invDet` computes their
inverse and determinant. -/
theorem invDet_val_of_posDef {L : Type u} [Field L] [PartialOrder L] [StarRing L]
    [IsOrderedRing L] [PosMulReflectLT L] (alg : MatMulAlgorithm L) {n : ℕ} (A : SqMat n L)
    (hA : A.PosDef) : (invDet alg A).val = (A⁻¹, A.det) :=
  invDet_val alg A fun j hj => (det_leading_pos_of_posDef hA j hj).ne'

theorem invDet_cost_le (alg : MatMulAlgorithm K) {n : ℕ} (A : SqMat n K) :
    (invDet alg A).cost.total ≤ BlockInverse.costBound alg (Nat.clog 2 n) := by
  simpa [invDet] using BlockInverse.invDet_cost_le alg _ _

/-- **Inversion and the determinant in `O(M(n))` operations**: under the regularity condition
`4 * M (2 ^ k) ≤ M (2 ^ (k + 1))`, `1 ≤ M 1` on the multiplication bound `M = alg.bound`,
`invDet` performs fewer than `5 * M (2 ^ ⌈log₂ n⌉)` operations. -/
theorem invDet_cost_le_bound (alg : MatMulAlgorithm K)
    (hreg : ∀ k, 4 * alg.bound (2 ^ k) ≤ alg.bound (2 ^ (k + 1))) (h1 : 1 ≤ alg.bound 1)
    {n : ℕ} (A : SqMat n K) :
    (invDet alg A).cost.total + 1 ≤ 5 * alg.bound (2 ^ Nat.clog 2 n) := by
  simpa [invDet] using BlockInverse.invDet_cost_le_bound alg hreg h1 _ _

/-- **Inversion and the determinant with a multiplication algorithm of exponent `ω`.** -/
theorem invDet_cost_le_rpow (alg : MatMulAlgorithm K)
    (hreg : ∀ k, 4 * alg.bound (2 ^ k) ≤ alg.bound (2 ^ (k + 1))) (h1 : 1 ≤ alg.bound 1)
    {ω C : ℝ} (hω : 0 ≤ ω) (hexp : alg.HasExponent ω C) {n : ℕ} (hn : 1 ≤ n)
    (A : SqMat n K) :
    ((invDet alg A).cost.total : ℝ) ≤ 5 * C * 2 ^ ω * (n : ℝ) ^ ω := by
  have hc := invDet_cost_le_bound alg hreg h1 A
  have hN : 1 ≤ 2 ^ Nat.clog 2 n := Nat.one_le_two_pow
  have hb := hexp _ hN
  have hC : 0 ≤ C := by
    have := hexp 1 le_rfl
    simp only [Nat.cast_one, Real.one_rpow, mul_one] at this
    exact le_trans (Nat.cast_nonneg _) this
  have h2n : ((2 ^ Nat.clog 2 n : ℕ) : ℝ) ≤ 2 * n := by exact_mod_cast two_pow_clog_le n hn
  have hpow : ((2 ^ Nat.clog 2 n : ℕ) : ℝ) ^ ω ≤ 2 ^ ω * (n : ℝ) ^ ω := by
    rw [← Real.mul_rpow zero_le_two (Nat.cast_nonneg n)]
    exact Real.rpow_le_rpow (Nat.cast_nonneg _) h2n hω
  have hc' : ((invDet alg A).cost.total : ℝ) + 1 ≤ 5 * (alg.bound (2 ^ Nat.clog 2 n) : ℝ) := by
    exact_mod_cast hc
  calc ((invDet alg A).cost.total : ℝ) ≤ 5 * (alg.bound (2 ^ Nat.clog 2 n) : ℝ) := by linarith
    _ ≤ 5 * (C * ((2 ^ Nat.clog 2 n : ℕ) : ℝ) ^ ω) := by gcongr
    _ ≤ 5 * (C * (2 ^ ω * (n : ℝ) ^ ω)) := by gcongr
    _ = 5 * C * 2 ^ ω * (n : ℝ) ^ ω := by ring

/-! ### Strassen's algorithm -/

theorem strassen_bound_two_pow (k : ℕ) :
    (MatMulAlgorithm.strassen K).bound (2 ^ k) = 7 * 7 ^ k := by
  simp [MatMulAlgorithm.strassen, Nat.clog_pow 2 k one_lt_two]

/-- Strassen's bound satisfies the regularity condition. -/
theorem strassen_regular (k : ℕ) :
    4 * (MatMulAlgorithm.strassen K).bound (2 ^ k) ≤
      (MatMulAlgorithm.strassen K).bound (2 ^ (k + 1)) := by
  rw [strassen_bound_two_pow, strassen_bound_two_pow, pow_succ]
  omega

theorem strassen_bound_one : 1 ≤ (MatMulAlgorithm.strassen K).bound 1 := by
  simpa using strassen_bound_two_pow (K := K) 0 ▸ (by norm_num : 1 ≤ 7 * 7 ^ 0)

/-- **Inverse and determinant in `O(n ^ log₂ 7)` operations** with Strassen's algorithm. -/
theorem invDet_strassen_cost_le {n : ℕ} (hn : 1 ≤ n) (A : SqMat n K) :
    ((invDet (MatMulAlgorithm.strassen K) A).cost.total : ℝ) ≤
      245 * (n : ℝ) ^ Strassen.strassenExponent := by
  have hc := invDet_cost_le_bound (MatMulAlgorithm.strassen K) strassen_regular
    strassen_bound_one A
  rw [strassen_bound_two_pow] at hc
  have h7 := Strassen.seven_pow_clog_le n hn
  have hc' : ((invDet (MatMulAlgorithm.strassen K) A).cost.total : ℝ) + 1 ≤
      35 * ((7 ^ Nat.clog 2 n : ℕ) : ℝ) := by
    push_cast at hc ⊢; exact_mod_cast (by omega : _ + 1 ≤ 35 * 7 ^ Nat.clog 2 n)
  linarith

end FastDet

end

end FastGE
