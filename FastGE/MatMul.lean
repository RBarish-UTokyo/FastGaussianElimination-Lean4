module

public import FastGE.Naive
public import FastGE.Strassen
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Nat.Log

/-!
# Matrix multiplication algorithms with a cost bound

`MatMulAlgorithm`, `HasExponent`, `Pad.pad`, `Pad.unpad`, `Strassen.strassenPad` and
`Strassen.strassenExponent` are defined in `FastGE/Spec.lean`.

A `MatMulAlgorithm R` bundles a multiplication procedure for `n × n` matrices over a ring `R`,
written in the counting monad `Counted`, with a proof that it computes the matrix product and
a monotone bound `bound n` on the number of ring operations it performs on `n × n` inputs.
Algorithms built on top of matrix multiplication can take a `MatMulAlgorithm` as a parameter
and express their cost in terms of `bound`.

`MatMulAlgorithm.HasExponent alg ω C` states `bound n ≤ C * n ^ ω` for all `n ≥ 1`.

## Instances

* `MatMulAlgorithm.naive`: schoolbook multiplication, `bound n = 2 * n ^ 3`, exponent `3`.
* `MatMulAlgorithm.strassen`: Strassen's algorithm [V. Strassen, *Gaussian elimination is not
  optimal*, Numer. Math. 13 (1969), 354–356] on inputs padded with zeros to the next power of
  two, `bound n = 7 * 7 ^ Nat.clog 2 n`, exponent `ω₀ = log₂ 7`
  (`strassenExponent`, with `strassenExponent < 3`).

## Padding

`pad h A` embeds an `n × n` matrix as the upper left block of an `N × N` matrix (`h : n ≤ N`),
with zeros elsewhere, and `unpad h` extracts the upper left block; `unpad_pad_mul` states
`unpad h (pad h A * pad h B) = A * B`.  Padding and unpadding only move entries and are free in
the cost model.
-/

namespace FastGE

open WordRAM.Algebraic

@[expose] public section

universe u

namespace MatMulAlgorithm

variable {R : Type u} [Ring R]

theorem HasExponent.cost_le {alg : MatMulAlgorithm R} {ω C : ℝ} (h : alg.HasExponent ω C)
    {n : ℕ} (hn : 1 ≤ n) (A B : SqMat n R) : ((alg.mul n A B).cost.total : ℝ) ≤ C * (n : ℝ) ^ ω :=
  le_trans (by exact_mod_cast alg.cost_le n A B) (h n hn)

end MatMulAlgorithm

/-! ### Schoolbook multiplication -/

namespace MatMulAlgorithm

variable (R : Type u) [Ring R]

/-- Schoolbook multiplication as a `MatMulAlgorithm`. -/
def naive : MatMulAlgorithm R where
  mul := Naive.mul
  mul_val := Naive.mul_val
  bound n := 2 * n ^ 3
  bound_mono _ _ h := Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left h 3)
  cost_le := Naive.mul_total_le

theorem naive_hasExponent : (naive R).HasExponent 3 2 := by
  intro n _
  simp [naive]

end MatMulAlgorithm

/-! ### Padding -/

namespace Pad

variable {R : Type u} {n N : ℕ}

@[simp] theorem unpad_pad [Zero R] (h : n ≤ N) (A : SqMat n R) : unpad h (pad h A) = A := by
  simp [pad, unpad]

/-- The product of padded matrices contains the product of the original matrices. -/
theorem unpad_pad_mul [NonUnitalNonAssocSemiring R] (h : n ≤ N) (A B : SqMat n R) :
    unpad h (pad h A * pad h B) = A * B := by
  have hmul : ∀ X Y : SqMat N R, Matrix.reindex (equiv h) (equiv h) (X * Y) =
      Matrix.reindex (equiv h) (equiv h) X * Matrix.reindex (equiv h) (equiv h) Y := by
    intro X Y
    simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv]
  rw [unpad, hmul, pad, pad, Equiv.apply_symm_apply, Equiv.apply_symm_apply,
    Matrix.fromBlocks_multiply, Matrix.toBlocks_fromBlocks₁₁]
  simp

end Pad

/-! ### Strassen's algorithm for all sizes -/

namespace Strassen

variable {R : Type u} [Ring R]

theorem strassenPad_val (n : ℕ) (A B : SqMat n R) : (strassenPad n A B).val = A * B := by
  simp [strassenPad, strassen_val, Pad.unpad_pad_mul]

theorem strassenPad_cost (n : ℕ) (A B : SqMat n R) :
    (strassenPad n A B).cost = ⟨adds (Nat.clog 2 n), 7 ^ Nat.clog 2 n⟩ := by
  simp [strassenPad, strassen_cost]

/-- Strassen's algorithm on `n × n` matrices performs at most `7 * 7 ^ Nat.clog 2 n`
operations. -/
theorem strassenPad_total_le (n : ℕ) (A B : SqMat n R) :
    (strassenPad n A B).cost.total ≤ 7 * 7 ^ Nat.clog 2 n := by
  simpa [strassenPad] using strassen_total_le (Nat.clog 2 n) (Pad.pad (le_two_pow_clog n) A)
    (Pad.pad (le_two_pow_clog n) B)

theorem strassenExponent_nonneg : 0 ≤ strassenExponent :=
  Real.logb_nonneg one_lt_two (by norm_num)

theorem strassenExponent_lt_three : strassenExponent < 3 := by
  rw [strassenExponent, Real.logb_lt_iff_lt_rpow one_lt_two (by norm_num)]
  norm_num

/-- `7 ^ m = (2 ^ m) ^ log₂ 7`. -/
theorem seven_pow_eq (m : ℕ) : (7 : ℝ) ^ m = ((2 : ℝ) ^ m) ^ strassenExponent := by
  rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul zero_le_two, mul_comm,
    Real.rpow_mul zero_le_two, strassenExponent, Real.rpow_logb two_pos (by norm_num)
      (by norm_num)]

/-- Rounding up to a power of two costs at most a factor `7` in `7 ^ k`:
`7 ^ Nat.clog 2 n ≤ 7 * n ^ log₂ 7` for `n ≥ 1`. -/
theorem seven_pow_clog_le (n : ℕ) (hn : 1 ≤ n) :
    ((7 ^ Nat.clog 2 n : ℕ) : ℝ) ≤ 7 * (n : ℝ) ^ strassenExponent := by
  rcases Nat.eq_or_lt_of_le hn with rfl | hn
  · simp
  have hk : 0 < Nat.clog 2 n := Nat.clog_pos one_lt_two hn
  have hlt := Nat.pow_pred_clog_lt_self one_lt_two hn
  obtain ⟨m, hm⟩ : ∃ m, Nat.clog 2 n = m + 1 := ⟨Nat.clog 2 n - 1, by omega⟩
  rw [hm, Nat.pred_eq_sub_one, Nat.add_sub_cancel] at hlt
  rw [hm]
  push_cast
  rw [pow_succ, mul_comm, seven_pow_eq]
  gcongr
  · exact strassenExponent_nonneg
  · exact_mod_cast hlt.le

end Strassen

namespace MatMulAlgorithm

variable (R : Type u) [Ring R]

/-- Strassen's algorithm, with zero padding to the next power of two, as a
`MatMulAlgorithm`. -/
def strassen : MatMulAlgorithm R where
  mul := Strassen.strassenPad
  mul_val := Strassen.strassenPad_val
  bound n := 7 * 7 ^ Nat.clog 2 n
  bound_mono _ _ h :=
    Nat.mul_le_mul_left 7 (Nat.pow_le_pow_right (by norm_num) (Nat.clog_mono_right 2 h))
  cost_le := Strassen.strassenPad_total_le

/-- Strassen's algorithm multiplies `n × n` matrices with at most `49 * n ^ log₂ 7`
operations. -/
theorem strassen_hasExponent : (strassen R).HasExponent Strassen.strassenExponent 49 := by
  intro n hn
  have := Strassen.seven_pow_clog_le n hn
  simp only [strassen, Nat.cast_mul, Nat.cast_ofNat]
  linarith

end MatMulAlgorithm

end

end FastGE
