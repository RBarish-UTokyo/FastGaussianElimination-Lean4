module

public import WordRAM.Algebraic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Matrix.Mul

/-!
# Naive matrix multiplication

The schoolbook algorithm in the counting monad `Counted`: every entry of the product of two
`n × n` matrices is a dot product of length `n`, computed with `n` multiplications and
`n - 1` additions.  In total it uses `n ^ 3` multiplications and `n ^ 2 * (n - 1)` additions.

## Main definitions

* `FastGE.Naive.dot n u v`: the dot product of two vectors of length `n`.
* `FastGE.Naive.mul n A B`: the product of two `n × n` matrices.

## Main results

* `FastGE.Naive.mul_val`: `(mul n A B).val = A * B`.
* `FastGE.Naive.mul_cost`: `(mul n A B).cost = ⟨n * n * (n - 1), n * n * n⟩`.
* `FastGE.Naive.mul_total_le`: the total number of operations is at most `2 * n ^ 3`.
-/

namespace FastGE

open WordRAM.Algebraic

@[expose] public section

universe u

namespace Naive

variable {R : Type u}

/-- Dot product of two vectors of length `n + 1`, accumulated from the right:
`n + 1` multiplications and `n` additions. -/
def dotSucc [Add R] [Mul R] : (n : ℕ) → (Fin (n + 1) → R) → (Fin (n + 1) → R) → Counted R
  | 0, u, v => Op.mul (u 0) (v 0)
  | n + 1, u, v => do
      let p ← Op.mul (u 0) (v 0)
      let s ← dotSucc n (Fin.tail u) (Fin.tail v)
      Op.add p s

/-- Dot product of two vectors of length `n`; the empty dot product is `0` and is free. -/
def dot [AddCommMonoid R] [Mul R] : (n : ℕ) → (Fin n → R) → (Fin n → R) → Counted R
  | 0, _, _ => pure 0
  | n + 1, u, v => dotSucc n u v

theorem dotSucc_val [NonUnitalNonAssocSemiring R] :
    ∀ (n : ℕ) (u v : Fin (n + 1) → R), (dotSucc n u v).val = ∑ i, u i * v i
  | 0, u, v => by simp [dotSucc]
  | n + 1, u, v => by
    rw [Fin.sum_univ_succ]
    simp [dotSucc, dotSucc_val n, Fin.tail]

theorem dotSucc_cost [Add R] [Mul R] :
    ∀ (n : ℕ) (u v : Fin (n + 1) → R), (dotSucc n u v).cost = ⟨n, n + 1⟩
  | 0, u, v => rfl
  | n + 1, u, v => by
    simp only [dotSucc, Counted.cost_bind, Op.cost_mul, Op.cost_add, dotSucc_cost n]
    ext <;> simp only [OpCount.adds_add, OpCount.muls_add] <;> omega

@[simp] theorem dot_val [NonUnitalNonAssocSemiring R] (n : ℕ) (u v : Fin n → R) :
    (dot n u v).val = ∑ i, u i * v i := by
  cases n with
  | zero => simp [dot]
  | succ n => exact dotSucc_val n u v

@[simp] theorem dot_cost [AddCommMonoid R] [Mul R] (n : ℕ) (u v : Fin n → R) :
    (dot n u v).cost = ⟨n - 1, n⟩ := by
  cases n with
  | zero => rfl
  | succ n => simpa [dot] using dotSucc_cost n u v

/-- Schoolbook multiplication of two `n × n` matrices: one dot product per entry. -/
def mul [NonUnitalNonAssocSemiring R] (n : ℕ) (A B : SqMat n R) : Counted (SqMat n R) :=
  Matrix.of <$> Counted.pi fun i => Counted.pi fun j => dot n (fun l => A i l) (fun l => B l j)

/-- **Correctness of schoolbook multiplication.** -/
theorem mul_val [NonUnitalNonAssocSemiring R] (n : ℕ) (A B : SqMat n R) :
    (mul n A B).val = A * B := by
  ext i j
  simp [mul, Matrix.mul_apply]

/-- **Operation count of schoolbook multiplication**: `n ^ 2 * (n - 1)` additions and
`n ^ 3` multiplications. -/
theorem mul_cost [NonUnitalNonAssocSemiring R] (n : ℕ) (A B : SqMat n R) :
    (mul n A B).cost = ⟨n * n * (n - 1), n * n * n⟩ := by
  ext <;> simp [mul, Finset.card_univ, Nat.mul_assoc]

/-- Schoolbook multiplication uses exactly `n ^ 3` multiplications. -/
theorem mul_muls [NonUnitalNonAssocSemiring R] (n : ℕ) (A B : SqMat n R) :
    (mul n A B).cost.muls = n ^ 3 := by
  simp [mul_cost, pow_three, Nat.mul_assoc]

/-- Schoolbook multiplication uses at most `2 * n ^ 3` operations. -/
theorem mul_total_le [NonUnitalNonAssocSemiring R] (n : ℕ) (A B : SqMat n R) :
    (mul n A B).cost.total ≤ 2 * n ^ 3 := by
  rw [mul_cost, OpCount.total_mk, pow_three, two_mul, ← Nat.mul_assoc]
  exact Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.sub_le n 1)) _

end Naive

end

end FastGE
