module

public import FastGE.FastDissection
public import PlanarSeparator.Square

/-!
# Fast nested dissection for plane graphs and their squares

The separator tree hypothesis of `FastGE.FastDissection.nestedDissection_fast` (separators and
boundaries of size `O(√m)` at every node with `m` vertices, parts of at most `2m/3` vertices) is
discharged for plane graphs by `PlanarSeparator.exists_sepTree` (constant `50000`) and for
squares of plane graphs of maximum degree at most `Δ` by `PlanarSeparator.exists_sepTree_square`
(constant `40 (1062 (Δ + 1)² + 1)`). Block elimination along the tree then computes the
determinant with `O(n ^ (ω / 2))` operations for a multiplication algorithm of exponent `ω > 2`.

The regularity of the elimination is a hypothesis on the matrix and the tree: it holds for
positive definite matrices, and whenever all pivots in the nested dissection order are nonzero.
-/

namespace FastGE

open WordRAM.Algebraic Matrix NestedDissection NestedDissection.SepTree FastGE.Frontal
  PlanarSeparator

@[expose] public section

universe u

namespace FastDissection

variable {K : Type u} [Field K] {n : ℕ}

/-- **Fast nested dissection for plane graphs.** For a plane graph `G` on `Fin n` there is a
separator tree `t` such that for every matrix `A` whose off-diagonal nonzero entries are edges of
`G` and for which block elimination along `t` is regular, it computes `det A` with
`O(n ^ (ω / 2))` operations. -/
theorem planar_nestedDissection_fast (alg : MatMulAlgorithm K)
    (hreg : ∀ k, 4 * alg.bound (2 ^ k) ≤ alg.bound (2 ^ (k + 1))) (h1 : 1 ≤ alg.bound 1)
    {ω C : ℝ} (hω : 2 < ω) (hexp : alg.HasExponent ω C) {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] {R : Kasteleyn.RotationSystem G} (hR : R.IsPlane) :
    ∃ (t : SepTree (Fin n)) (_hd : IsDissection G t) (_hv : t.verts = Finset.univ),
      ∀ A : Matrix (Fin n) (Fin n) K, (∀ x y, x ≠ y → A x y ≠ 0 → G.Adj x y) →
        AllNodes (NodeRegular A) t →
        (ndCounted G alg A t).val.1 = A.det ∧
          ((ndCounted G alg A t).cost.total : ℝ) ≤
            (5 * C * 2 ^ ω + 2 * C + 2) * (treeConst + treeConst + 1) ^ ω /
              (1 - (2 / 3 : ℝ) ^ (ω / 2 - 1)) * (n : ℝ) ^ (ω / 2) := by
  obtain ⟨t, hv, hd, hsq, hs⟩ := exists_sepTree (G := G) hR
  refine ⟨t, hd, hv, fun A hA hr => ?_⟩
  simpa using nestedDissection_fast alg hreg h1 hω hexp (by norm_num [treeConst])
    (by norm_num [treeConst]) t hd hv hsq hs A hA hr

/-- **Fast nested dissection for plane graphs, with nonzero pivots.** -/
theorem planar_nestedDissection_fast_of_pivotsIn (alg : MatMulAlgorithm K)
    (hreg : ∀ k, 4 * alg.bound (2 ^ k) ≤ alg.bound (2 ^ (k + 1))) (h1 : 1 ≤ alg.bound 1)
    {ω C : ℝ} (hω : 2 < ω) (hexp : alg.HasExponent ω C) {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] {R : Kasteleyn.RotationSystem G} (hR : R.IsPlane) :
    ∃ (t : SepTree (Fin n)) (hd : IsDissection G t) (hv : t.verts = Finset.univ),
      ∀ A : Matrix (Fin n) (Fin n) K, (∀ x y, x ≠ y → A x y ≠ 0 → G.Adj x y) →
        (∀ k : Fin n, pivotsIn (ndPerm t hd hv) A k ≠ 0) →
        (ndCounted G alg A t).val.1 = A.det ∧
          ((ndCounted G alg A t).cost.total : ℝ) ≤
            (5 * C * 2 ^ ω + 2 * C + 2) * (treeConst + treeConst + 1) ^ ω /
              (1 - (2 / 3 : ℝ) ^ (ω / 2 - 1)) * (n : ℝ) ^ (ω / 2) := by
  obtain ⟨t, hv, hd, hsq, hs⟩ := exists_sepTree (G := G) hR
  exact ⟨t, hd, hv, fun A hA hpiv => nestedDissection_fast_of_pivotsIn alg hreg h1 hω hexp
    (by norm_num [treeConst]) (by norm_num [treeConst]) t hd hv hsq hs A hA hpiv⟩

/-- **Fast nested dissection for squares of plane graphs of bounded degree.** For a plane graph
`G` on `Fin n` of maximum degree at most `Δ` there is a separator tree `t` of its square such that
for every matrix `A` whose off-diagonal nonzero entries join vertices at distance at most `2` in
`G` and for which block elimination along `t` is regular, it computes `det A` with
`O(n ^ (ω / 2))` operations. -/
theorem square_nestedDissection_fast (alg : MatMulAlgorithm K)
    (hreg : ∀ k, 4 * alg.bound (2 ^ k) ≤ alg.bound (2 ^ (k + 1))) (h1 : 1 ≤ alg.bound 1)
    {ω C : ℝ} (hω : 2 < ω) (hexp : alg.HasExponent ω C) {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] {R : Kasteleyn.RotationSystem G} (hR : R.IsPlane) {Δ : ℕ}
    (hΔ : ∀ v, G.degree v ≤ Δ) :
    ∃ (t : SepTree (Fin n)) (_hd : IsDissection (square G) t) (_hv : t.verts = Finset.univ),
      ∀ A : Matrix (Fin n) (Fin n) K, (∀ x y, x ≠ y → A x y ≠ 0 → (square G).Adj x y) →
        AllNodes (NodeRegular A) t →
        (ndCounted (square G) alg A t).val.1 = A.det ∧
          ((ndCounted (square G) alg A t).cost.total : ℝ) ≤
            (5 * C * 2 ^ ω + 2 * C + 2) * (squareTreeConst Δ + squareTreeConst Δ + 1) ^ ω /
              (1 - (2 / 3 : ℝ) ^ (ω / 2 - 1)) * (n : ℝ) ^ (ω / 2) := by
  obtain ⟨t, hv, hd, hsq, hs⟩ := exists_sepTree_square hR hΔ
  have hT : 0 ≤ squareTreeConst Δ := by rw [squareTreeConst]; positivity
  refine ⟨t, hd, hv, fun A hA hr => ?_⟩
  simpa using nestedDissection_fast alg hreg h1 hω hexp hT hT t hd hv hsq hs A hA hr

/-- **Fast nested dissection for squares of plane graphs of bounded degree, with nonzero
pivots.** -/
theorem square_nestedDissection_fast_of_pivotsIn (alg : MatMulAlgorithm K)
    (hreg : ∀ k, 4 * alg.bound (2 ^ k) ≤ alg.bound (2 ^ (k + 1))) (h1 : 1 ≤ alg.bound 1)
    {ω C : ℝ} (hω : 2 < ω) (hexp : alg.HasExponent ω C) {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] {R : Kasteleyn.RotationSystem G} (hR : R.IsPlane) {Δ : ℕ}
    (hΔ : ∀ v, G.degree v ≤ Δ) :
    ∃ (t : SepTree (Fin n)) (hd : IsDissection (square G) t) (hv : t.verts = Finset.univ),
      ∀ A : Matrix (Fin n) (Fin n) K, (∀ x y, x ≠ y → A x y ≠ 0 → (square G).Adj x y) →
        (∀ k : Fin n, pivotsIn (ndPerm t hd hv) A k ≠ 0) →
        (ndCounted (square G) alg A t).val.1 = A.det ∧
          ((ndCounted (square G) alg A t).cost.total : ℝ) ≤
            (5 * C * 2 ^ ω + 2 * C + 2) * (squareTreeConst Δ + squareTreeConst Δ + 1) ^ ω /
              (1 - (2 / 3 : ℝ) ^ (ω / 2 - 1)) * (n : ℝ) ^ (ω / 2) := by
  obtain ⟨t, hv, hd, hsq, hs⟩ := exists_sepTree_square hR hΔ
  have hT : 0 ≤ squareTreeConst Δ := by rw [squareTreeConst]; positivity
  exact ⟨t, hd, hv, fun A hA hpiv => nestedDissection_fast_of_pivotsIn alg hreg h1 hω hexp
    hT hT t hd hv hsq hs A hA hpiv⟩

/-- **Fast nested dissection for positive definite matrices on squares of plane graphs of bounded
degree** (e.g. `Kᵀ K` for a real matrix `K` of full rank with pattern `G`): the determinant in
`O(n ^ (ω / 2))` operations, with no regularity hypothesis. -/
theorem square_nestedDissection_fast_of_posDef {L : Type u} [Field L] [PartialOrder L]
    [StarRing L] [IsOrderedRing L] [PosMulReflectLT L] (alg : MatMulAlgorithm L)
    (hreg : ∀ k, 4 * alg.bound (2 ^ k) ≤ alg.bound (2 ^ (k + 1))) (h1 : 1 ≤ alg.bound 1)
    {ω C : ℝ} (hω : 2 < ω) (hexp : alg.HasExponent ω C) {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] {R : Kasteleyn.RotationSystem G} (hR : R.IsPlane) {Δ : ℕ}
    (hΔ : ∀ v, G.degree v ≤ Δ) :
    ∃ (t : SepTree (Fin n)) (_hd : IsDissection (square G) t) (_hv : t.verts = Finset.univ),
      ∀ A : Matrix (Fin n) (Fin n) L, (∀ x y, x ≠ y → A x y ≠ 0 → (square G).Adj x y) →
        A.PosDef →
        (ndCounted (square G) alg A t).val.1 = A.det ∧
          ((ndCounted (square G) alg A t).cost.total : ℝ) ≤
            (5 * C * 2 ^ ω + 2 * C + 2) * (squareTreeConst Δ + squareTreeConst Δ + 1) ^ ω /
              (1 - (2 / 3 : ℝ) ^ (ω / 2 - 1)) * (n : ℝ) ^ (ω / 2) := by
  obtain ⟨t, hd, hv, h⟩ := square_nestedDissection_fast alg hreg h1 hω hexp hR hΔ
  exact ⟨t, hd, hv, fun A hA hpd => h A hA (allNodes_nodeRegular_of_posDef hpd t)⟩

end FastDissection

end

end FastGE
