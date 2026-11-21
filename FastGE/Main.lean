module

public import FastGE.Spec
public import FastGE.Planar

/-!
# The targets of `FastGE/Spec.lean`

The targets are stated in `FastGE/Spec.lean`; this file proves them from the library.

* `FastGE.strassen_count` (`StrassenCount`): `FastGE.Strassen.strassen_val`,
  `FastGE.Strassen.strassen_cost` and `FastGE.Strassen.adds_eq`.
* `FastGE.strassen_exponent` (`StrassenExponent`): the algorithm
  `FastGE.MatMulAlgorithm.strassen` and `FastGE.MatMulAlgorithm.strassen_hasExponent`.
* `FastGE.inverse_determinant` (`InverseDeterminant`): `FastGE.FastDet.invDet_val`,
  `FastGE.FastDet.invDet_cost_le_bound` and `FastGE.FastDet.invDet_cost_le_rpow`.
* `FastGE.planar_fast_determinant`, `FastGE.square_fast_determinant` and
  `FastGE.square_fast_determinant_posDef`: `FastGE.FastDissection.planar_nestedDissection_fast`,
  `FastGE.FastDissection.square_nestedDissection_fast` and
  `FastGE.FastDissection.square_nestedDissection_fast_of_posDef`.
-/

@[expose] public section

namespace FastGE

open WordRAM.Algebraic

universe u

/-- **Strassen's algorithm and its exact operation count.** -/
theorem strassen_count : StrassenCount.{u} := by
  intro R _ k A B
  exact ⟨Strassen.strassen_val k A B, by rw [Strassen.strassen_cost, Strassen.adds_eq]⟩

/-- The bound of Strassen's algorithm on powers of two. -/
theorem strassen_bound_two_pow (R : Type u) [Ring R] (k : ℕ) :
    (MatMulAlgorithm.strassen R).bound (2 ^ k) = 7 * 7 ^ k := by
  simp [MatMulAlgorithm.strassen, Nat.clog_pow 2 k one_lt_two]

/-- **The exponent of Strassen's algorithm.** -/
theorem strassen_exponent : StrassenExponent.{u} := by
  refine ⟨⟨FastDissection.two_lt_strassenExponent, Strassen.strassenExponent_lt_three⟩,
    fun R _ => ⟨MatMulAlgorithm.strassen R, rfl, MatMulAlgorithm.strassen_hasExponent R,
      fun k => ?_, ?_⟩⟩
  · rw [strassen_bound_two_pow, strassen_bound_two_pow, pow_succ]
    omega
  · have := strassen_bound_two_pow R 0
    simp only [pow_zero] at this
    omega

/-- **Inverse and determinant in `O(M(n))` operations.** -/
theorem inverse_determinant : InverseDeterminant.{u} := by
  intro K _ alg hreg h1 n A
  exact ⟨FastDet.invDet_val alg A, FastDet.invDet_cost_le_bound alg hreg h1 A,
    fun hω hexp hn => FastDet.invDet_cost_le_rpow alg hreg h1 hω hexp hn A⟩

/-- **Fast nested dissection for plane graphs.** -/
theorem planar_fast_determinant : PlanarFastDeterminant.{u} := by
  intro K _ alg hreg h1 ω C hω hexp n G _ R hR
  obtain ⟨t, hd, hv, h⟩ := FastDissection.planar_nestedDissection_fast alg hreg h1 hω hexp hR
  exact ⟨t, hd, hv, h⟩

/-- **Fast nested dissection for squares of plane graphs of bounded degree.** -/
theorem square_fast_determinant : SquareFastDeterminant.{u} := by
  intro K _ alg hreg h1 ω C hω hexp n G _ R hR Δ hΔ
  obtain ⟨t, hd, hv, h⟩ := FastDissection.square_nestedDissection_fast alg hreg h1 hω hexp hR hΔ
  exact ⟨t, hd, hv, h⟩

/-- **Fast nested dissection for positive definite matrices on squares of plane graphs of bounded
degree.** -/
theorem square_fast_determinant_posDef : SquareFastDeterminantPosDef.{u} := by
  intro L _ _ _ _ _ alg hreg h1 ω C hω hexp n G _ R hR Δ hΔ
  obtain ⟨t, hd, hv, h⟩ :=
    FastDissection.square_nestedDissection_fast_of_posDef alg hreg h1 hω hexp hR hΔ
  exact ⟨t, hd, hv, h⟩

end FastGE

end
