module

public import FastGE.Spec
public import WordRAM.Algebraic
public import Mathlib.Data.Matrix.Block
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Tactic.NoncommRing
public import Mathlib.Tactic.Ring

/-!
# Strassen's matrix multiplication

Strassen's algorithm [V. Strassen, *Gaussian elimination is not optimal*, Numer. Math. 13
(1969), 354–356] multiplies two `2 × 2` block matrices with seven block multiplications and
eighteen block additions/subtractions instead of eight multiplications and four additions.
Applied recursively to matrices of size `2 ^ k` it uses `7 ^ k` scalar multiplications.

The algorithm is written in the counting monad `Counted`, so its operation count is read off
the algorithm itself.  Only the ring axioms are used (no commutativity): the recursion
multiplies matrix blocks, which do not commute.

## Main definitions

These definitions are in `FastGE/Spec.lean`, except `adds`.

* `FastGE.Strassen.halves k : Fin (2 ^ (k + 1)) ≃ Fin (2 ^ k) ⊕ Fin (2 ^ k)`, splitting an
  index range into its first and second half; `split` and `join` are the corresponding
  block decomposition and recomposition (free in the cost model: they only move entries).
* `FastGE.Strassen.strassen k A B`: the recursive algorithm.
* `FastGE.Strassen.adds k`: the number of additive operations, given by the recurrence
  `adds (k + 1) = 7 * adds k + 18 * 4 ^ k`.

## Main results

* `FastGE.Strassen.strassen_val`: `(strassen k A B).val = A * B`.
* `FastGE.Strassen.strassen_cost`: `(strassen k A B).cost = ⟨adds k, 7 ^ k⟩`.
* `FastGE.Strassen.adds_eq`: `adds k = 6 * (7 ^ k - 4 ^ k)`.
* `FastGE.Strassen.strassen_total`: the total number of operations is `7 * 7 ^ k - 6 * 4 ^ k`.
* `FastGE.Strassen.strassen_total_le`: the total number of operations is at most `7 * 7 ^ k`.
-/

namespace FastGE

open WordRAM.Algebraic

@[expose] public section

universe u

namespace Strassen

variable {R : Type u}

/-! ### Block decomposition -/

theorem join_eq_iff {k : ℕ} (C₁₁ C₁₂ C₂₁ C₂₂ : SqMat (2 ^ k) R) (M : SqMat (2 ^ (k + 1)) R) :
    join C₁₁ C₁₂ C₂₁ C₂₂ = M ↔ Matrix.fromBlocks C₁₁ C₁₂ C₂₁ C₂₂ = split M := by
  rw [join, split, Equiv.symm_apply_eq, eq_comm]

theorem split_mul [NonUnitalNonAssocSemiring R] {k : ℕ} (A B : SqMat (2 ^ (k + 1)) R) :
    split (A * B) = split A * split B := by
  simp only [split, Matrix.reindex_apply, Matrix.submatrix_mul_equiv]

/-- Strassen's identities for `2 × 2` block matrices over an arbitrary ring. -/
theorem fromBlocks_mul_eq {m : Type*} [Fintype m] [DecidableEq m] [Ring R]
    (A₁₁ A₁₂ A₂₁ A₂₂ B₁₁ B₁₂ B₂₁ B₂₂ : Matrix m m R) :
    Matrix.fromBlocks A₁₁ A₁₂ A₂₁ A₂₂ * Matrix.fromBlocks B₁₁ B₁₂ B₂₁ B₂₂ =
      Matrix.fromBlocks
        ((A₁₁ + A₂₂) * (B₁₁ + B₂₂) + A₂₂ * (B₂₁ - B₁₁) - (A₁₁ + A₁₂) * B₂₂ +
          (A₁₂ - A₂₂) * (B₂₁ + B₂₂))
        (A₁₁ * (B₁₂ - B₂₂) + (A₁₁ + A₁₂) * B₂₂)
        ((A₂₁ + A₂₂) * B₁₁ + A₂₂ * (B₂₁ - B₁₁))
        ((A₁₁ + A₂₂) * (B₁₁ + B₂₂) - (A₂₁ + A₂₂) * B₁₁ + A₁₁ * (B₁₂ - B₂₂) +
          (A₂₁ - A₁₁) * (B₁₁ + B₁₂)) := by
  rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_inj]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> noncomm_ring

/-! ### The algorithm -/

/-! ### Correctness -/

/-- **Correctness of Strassen's algorithm.** -/
theorem strassen_val [Ring R] : ∀ (k : ℕ) (A B : SqMat (2 ^ k) R),
    (strassen k A B).val = A * B
  | 0, A, B => by
    have h : ∀ i : Fin (2 ^ 0), i = ⟨0, Nat.two_pow_pos 0⟩ := fun i =>
      Fin.ext (by have := i.2; simp only [pow_zero] at this; omega)
    ext i j
    simp only [strassen, Counted.val_bind, Op.val_mul, Counted.val_pure, Matrix.of_apply,
      Matrix.mul_apply]
    rw [Finset.sum_eq_single ⟨0, Nat.two_pow_pos 0⟩ (fun l _ hl => absurd (h l) hl)
      (fun hl => absurd (Finset.mem_univ _) hl), h i, h j]
  | k + 1, A, B => by
    simp only [strassen, Counted.val_bind, Counted.val_pure, Mat.val_add, Mat.val_sub,
      strassen_val k]
    rw [join_eq_iff, split_mul]
    conv_rhs => rw [← Matrix.fromBlocks_toBlocks (split A), ← Matrix.fromBlocks_toBlocks (split B)]
    rw [fromBlocks_mul_eq]

/-! ### Operation count -/

/-- The number of additive operations of `strassen k`: eighteen additions of blocks of size
`2 ^ k` (each costing `4 ^ k`) at the top level, plus seven recursive calls. -/
def adds : ℕ → ℕ
  | 0 => 0
  | k + 1 => 7 * adds k + 18 * 4 ^ k

@[simp] theorem adds_zero : adds 0 = 0 := rfl

theorem adds_succ (k : ℕ) : adds (k + 1) = 7 * adds k + 18 * 4 ^ k := rfl

/-- Closed form of the addition count, without subtraction. -/
theorem adds_add_eq (k : ℕ) : adds k + 6 * 4 ^ k = 6 * 7 ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [adds_succ, pow_succ, pow_succ]; omega

/-- Closed form of the addition count: `adds k = 6 * (7 ^ k - 4 ^ k)`. -/
theorem adds_eq (k : ℕ) : adds k = 6 * (7 ^ k - 4 ^ k) := by
  have := adds_add_eq k; omega

/-- **Operation count of Strassen's algorithm**: `adds k` additive operations and exactly
`7 ^ k` multiplications. -/
theorem strassen_cost [Ring R] : ∀ (k : ℕ) (A B : SqMat (2 ^ k) R),
    (strassen k A B).cost = ⟨adds k, 7 ^ k⟩
  | 0, A, B => by simp [strassen]
  | k + 1, A, B => by
    have h4 : (4 : ℕ) ^ k = 2 ^ k * 2 ^ k := by rw [← mul_pow]; norm_num
    simp only [strassen, Counted.cost_bind, Counted.cost_pure,
      Mat.cost_add, Mat.cost_sub, Fintype.card_fin, strassen_cost k]
    refine OpCount.ext ?_ ?_
    · simp only [OpCount.adds_add, OpCount.adds_zero, adds_succ, h4]; ring
    · simp only [OpCount.muls_add, OpCount.muls_zero]; ring

/-- Strassen's algorithm uses exactly `7 ^ k` multiplications. -/
theorem strassen_muls [Ring R] (k : ℕ) (A B : SqMat (2 ^ k) R) :
    (strassen k A B).cost.muls = 7 ^ k := by
  simp [strassen_cost]

/-- Strassen's algorithm uses exactly `6 * (7 ^ k - 4 ^ k)` additive operations. -/
theorem strassen_adds [Ring R] (k : ℕ) (A B : SqMat (2 ^ k) R) :
    (strassen k A B).cost.adds = 6 * (7 ^ k - 4 ^ k) := by
  simp [strassen_cost, adds_eq]

/-- The total number of operations of Strassen's algorithm is `7 * 7 ^ k - 6 * 4 ^ k`. -/
theorem strassen_total [Ring R] (k : ℕ) (A B : SqMat (2 ^ k) R) :
    (strassen k A B).cost.total = 7 * 7 ^ k - 6 * 4 ^ k := by
  have := adds_add_eq k
  simp only [strassen_cost, OpCount.total_mk]
  omega

/-- The total number of operations of Strassen's algorithm is at most `7 * 7 ^ k`. -/
theorem strassen_total_le [Ring R] (k : ℕ) (A B : SqMat (2 ^ k) R) :
    (strassen k A B).cost.total ≤ 7 * 7 ^ k := by
  rw [strassen_total]; omega

end Strassen

end

end FastGE
