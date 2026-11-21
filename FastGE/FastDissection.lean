module

public import FastGE.Frontal
public import NestedDissection.Main
public import NestedDissection.PosDef

/-!
# Nested dissection with fast matrix multiplication

Block elimination along a separator tree [R. J. Lipton, D. J. Rose, R. E. Tarjan, *Generalized
nested dissection*, SIAM J. Numer. Anal. 16 (1979), 346–358; V. Pan, J. Reif, *Fast and
efficient parallel solution of sparse linear systems*, SIAM J. Comput. 22 (1993), 1227–1250;
M. Mucha, P. Sankowski, *Maximum matchings in planar graphs via Gaussian elimination*,
Algorithmica 45 (2006), 3–20].

Let `t` be a separator tree of a graph `G` on a finite linearly ordered vertex type `V`, and let
`A : Matrix V V K` have its off-diagonal nonzero entries on edges of `G`.  The tree is processed
bottom up.  At a node with separator `s`, parts `a`, `b` and boundary `Bd` (the vertices outside
the node adjacent to it), the corrections of the two parts (Schur complement updates, supported
on their boundaries) are combined, the separator block of the resulting frontal matrix is
inverted by fast block inversion, and the correction of the whole node is formed on `Bd` with two
products of size `|s| + |Bd|` (`FastGE.Frontal.frontStep`).  The determinant of `A` is the
product of the determinants of the separator blocks.

With separators and boundaries of size at most `α √m` and `β √m` at a node with `m` vertices, and
parts of size at most `2 m / 3`, a node costs `O(m ^ (ω / 2))` operations for a multiplication
algorithm of exponent `ω`; for `ω > 2` the costs decrease geometrically down the tree and the
total is `O(n ^ (ω / 2))`.

## Main definitions

These definitions are in `FastGE/Spec.lean`.

* `FastGE.FastDissection.partVerts t`: the vertices of the two parts of the root of `t`.
* `FastGE.FastDissection.NodeRegular A t`: the principal submatrices of `A` on the parts of the
  root of `t` together with an initial segment of its separator are invertible.
* `FastGE.FastDissection.ndCounted alg G A t`: the elimination, returning the determinant of the
  principal submatrix on the vertices of `t` and the correction of these vertices.

## Main results

* `FastGE.FastDissection.ndCounted_val`: correctness.
* `FastGE.FastDissection.ndCounted_cost_le`: the operation count is a sum over the nodes.
* `FastGE.FastDissection.ndCounted_cost_le_rpow`: the total operation count, for any matrix.
* `FastGE.FastDissection.sumNodes_rpow_le`: `∑ over nodes m ^ γ ≤ n ^ γ / (1 - (2/3) ^ (γ - 1))`
  for shrinking trees and `γ > 1`.
* `FastGE.FastDissection.nestedDissection_fast`: the determinant in
  `K₀ * (α + β + 1) ^ ω / (1 - (2/3) ^ (ω/2 - 1)) * n ^ (ω / 2)` operations, where
  `K₀ = 5 C 2 ^ ω + 2 C + 2` for a multiplication algorithm with exponent `ω > 2` and constant `C`.
* `FastGE.FastDissection.nestedDissection_strassen`: with Strassen's algorithm,
  `O(n ^ (log₂ 7 / 2))` operations.
* `FastGE.FastDissection.allNodes_nodeRegular_of_posDef`: positive definite matrices satisfy the
  regularity hypothesis.
* `FastGE.FastDissection.allNodes_nodeRegular_of_leading`,
  `FastGE.FastDissection.allNodes_nodeRegular_of_pivotsIn`: so do matrices whose leading
  principal minors (equivalently, pivots) in the nested dissection order are all nonzero.
* `FastGE.FastDissection.nestedDissection_fast_of_pivotsIn`: the main theorem under that
  hypothesis, for graphs on `Fin n`.
-/

namespace FastGE

open WordRAM.Algebraic Matrix NestedDissection NestedDissection.SepTree FastGE.Frontal

@[expose] public section

universe u

namespace FastDissection

variable {V : Type} [Fintype V] [LinearOrder V] {K : Type u} [Field K]

/-! ### The regularity hypothesis -/

omit [Fintype V] in
theorem partVerts_union_own (t : SepTree V) : partVerts t ∪ t.own = t.verts := by
  cases t with
  | leaf s => simp [partVerts, own, verts]
  | node s a b =>
    ext x
    simp only [partVerts, own, verts, Finset.mem_union]
    tauto

omit [Fintype V] in
theorem NodeRegular.det_ne_zero {A : Matrix V V K} {t : SepTree V} (h : NodeRegular A t) :
    (principal A t.verts).det ≠ 0 := by
  have := h t.own.card le_rfl
  rwa [initSeg_card, partVerts_union_own] at this

omit [Fintype V] in
/-- If all principal minors of `A` are nonzero, the block elimination meets only invertible
blocks. -/
theorem allNodes_nodeRegular_of_forall {A : Matrix V V K}
    (h : ∀ W : Finset V, (principal A W).det ≠ 0) (t : SepTree V) :
    AllNodes (NodeRegular A) t := by
  induction t with
  | leaf s => exact fun j _ => h _
  | node s a b iha ihb => exact ⟨fun j _ => h _, iha, ihb⟩

omit [Fintype V] in
/-- Positive definite matrices have positive principal minors, so the block elimination meets
only invertible blocks. -/
theorem allNodes_nodeRegular_of_posDef {L : Type u} [Field L] [PartialOrder L] [StarRing L]
    [IsOrderedRing L] [PosMulReflectLT L] {A : Matrix V V L} (hA : A.PosDef) (t : SepTree V) :
    AllNodes (NodeRegular A) t :=
  allNodes_nodeRegular_of_forall (fun _ => (hA.submatrix Subtype.val_injective).det_pos.ne') t

/-! ### The algorithm -/

variable (G : SimpleGraph V) [DecidableRel G.Adj]

variable {G}

theorem disjoint_bdry (W : Finset V) : Disjoint (bdry G W) W :=
  Finset.disjoint_left.mpr fun _ hx => (mem_bdry.mp hx).1

/-- Entries of `A` coupling `W` to a vertex outside `W` and its boundary vanish. -/
theorem sparse_of_not_mem_bdry {A : Matrix V V K} (hA : ∀ x y, x ≠ y → A x y ≠ 0 → G.Adj x y)
    (W : Finset V) {x : V} (hx : x ∉ W) (hxB : x ∉ bdry G W) {u : V} (hu : u ∈ W) :
    A x u = 0 ∧ A u x = 0 := by
  have hne : x ≠ u := fun h => hx (h ▸ hu)
  refine ⟨by_contra fun h => hxB ?_, by_contra fun h => hxB ?_⟩
  · exact mem_bdry.mpr ⟨hx, u, hu, (hA x u hne h).symm⟩
  · exact mem_bdry.mpr ⟨hx, u, hu, hA u x hne.symm h⟩

/-- **Correctness of block elimination along a separator tree.** -/
theorem ndCounted_val (alg : MatMulAlgorithm K) {A : Matrix V V K}
    (hA : ∀ x y, x ≠ y → A x y ≠ 0 → G.Adj x y) :
    ∀ (t : SepTree V), IsDissection G t → AllNodes (NodeRegular A) t →
      (ndCounted G alg A t).val.1 = (principal A t.verts).det ∧
        ∀ x y, x ∉ t.verts → y ∉ t.verts → (ndCounted G alg A t).val.2 x y = corr A t.verts x y
  | leaf s, _, hr => by
    by_cases hs : s = ∅
    · subst hs
      have e : ndCounted G alg A (leaf ∅) = pure (1, 0) := by simp [ndCounted]
      rw [e]
      exact ⟨(det_principal_empty A).symm, fun x y _ _ => by simp [verts]⟩
    rw [ndCounted, ite_eq_right hs]
    have h := frontStep_val alg A 0 0 1 1 (X := ∅) (s := s) (Bd := bdry G s)
      (Finset.disjoint_empty_left _) (by rw [Finset.empty_union]; exact disjoint_bdry s)
      (fun x hx hxB u hu => by
        rw [Finset.empty_union] at hx hu
        exact sparse_of_not_mem_bdry hA s hx hxB hu)
      (fun x y _ _ => by simp) (by simp) hr
    rw [Finset.empty_union] at h
    exact h
  | node s a b, hd, hr => by
    by_cases hv : (node s a b).verts = ∅
    · rw [ndCounted, ite_eq_left hv, hv]
      simp
    rw [ndCounted, ite_eq_right hv]
    obtain ⟨hsa, hsb, hab, hadj, hda, hdb⟩ := hd
    obtain ⟨hr₀, hra, hrb⟩ := hr
    obtain ⟨ha₁, ha₂⟩ := ndCounted_val alg hA a hda hra
    obtain ⟨hb₁, hb₂⟩ := ndCounted_val alg hA b hdb hrb
    have hW : (a.verts ∪ b.verts) ∪ s = (node s a b).verts := by
      exact partVerts_union_own (node s a b)
    have hzero : ∀ u ∈ a.verts, ∀ v ∈ b.verts, A u v = 0 ∧ A v u = 0 := by
      intro u hu v hv
      have hne : u ≠ v := fun h => Finset.disjoint_left.mp hab hu (h ▸ hv)
      refine ⟨by_contra fun h => hadj u hu v hv (hA u v hne h), by_contra fun h => ?_⟩
      exact hadj u hu v hv (hA v u hne.symm h).symm
    obtain ⟨hcorr, hdet⟩ := corr_union_of_zero A hab hzero hra.self.det_ne_zero
      hrb.self.det_ne_zero
    have h := frontStep_val alg A (ndCounted G alg A a).val.2 (ndCounted G alg A b).val.2
      (ndCounted G alg A a).val.1 (ndCounted G alg A b).val.1
      (X := a.verts ∪ b.verts) (s := s) (Bd := bdry G (node s a b).verts)
      (Finset.disjoint_union_left.mpr ⟨hsa.symm, hsb.symm⟩)
      (by rw [hW]; exact disjoint_bdry _)
      (fun x hx hxB u hu => by
        rw [hW] at hx hu
        exact sparse_of_not_mem_bdry hA _ hx hxB hu)
      (fun x y hx hy => by
        rw [Finset.mem_union, not_or] at hx hy
        rw [ha₂ x y hx.1 hy.1, hb₂ x y hx.2 hy.2, hcorr, Matrix.add_apply])
      (by rw [ha₁, hb₁, hdet]) hr₀
    rw [hW] at h
    exact h

/-- The number of operations spent at the root of `t` (none if `t` has no vertices). -/
def nodeCost (alg : MatMulAlgorithm K) (G : SimpleGraph V) [DecidableRel G.Adj]
    (t : SepTree V) : ℕ :=
  if t.verts = ∅ then 0 else frontCost alg t.own.card (bdry G t.verts).card

/-- **Operation count of block elimination along a separator tree**: the sum over the nodes of
the cost of one frontal step. -/
theorem ndCounted_cost_le (alg : MatMulAlgorithm K) (A : Matrix V V K) :
    ∀ t : SepTree V, (ndCounted G alg A t).cost.total ≤ t.sumNodes (nodeCost alg G)
  | leaf s => by
    by_cases hs : s = ∅
    · simp [ndCounted, hs]
    rw [ndCounted, ite_eq_right hs]
    simpa [sumNodes, nodeCost, verts, own, hs] using frontStep_cost_le alg A 0 0 1 1 s (bdry G s)
  | node s a b => by
    by_cases hv : (node s a b).verts = ∅
    · simp [ndCounted, hv]
    rw [ndCounted, ite_eq_right hv]
    have ha := ndCounted_cost_le alg A a
    have hb := ndCounted_cost_le alg A b
    have hf := frontStep_cost_le alg A (ndCounted G alg A a).val.2 (ndCounted G alg A b).val.2
      (ndCounted G alg A a).val.1 (ndCounted G alg A b).val.1 s (bdry G (node s a b).verts)
    simp only [Counted.cost_bind, OpCount.total_add, sumNodes, nodeCost, ite_eq_right hv, own]
    omega

/-! ### The cost bound -/

/-- The cost of a frontal step in terms of the exponent of the multiplication algorithm. -/
theorem frontCost_le (alg : MatMulAlgorithm K)
    (hreg : ∀ k, 4 * alg.bound (2 ^ k) ≤ alg.bound (2 ^ (k + 1))) (h1 : 1 ≤ alg.bound 1)
    {ω C : ℝ} (hω : 2 ≤ ω) (hexp : alg.HasExponent ω C) (p q : ℕ) :
    (frontCost alg p q : ℝ) ≤ (5 * C * 2 ^ ω + 2 * C + 2) * ((p + q + 1 : ℕ) : ℝ) ^ ω := by
  have hC : 0 ≤ C := by
    have := hexp 1 le_rfl
    simp only [Nat.cast_one, Real.one_rpow, mul_one] at this
    exact le_trans (Nat.cast_nonneg _) this
  have hcb := BlockInverse.costBound_add_one_le alg hreg h1 (Nat.clog 2 p)
  set N := 2 ^ Nat.clog 2 p with hN
  have hN1 : 1 ≤ N := Nat.one_le_two_pow
  have hN2 : N ≤ 2 * (p + q + 1) := by
    rcases Nat.eq_zero_or_pos p with hp | hp
    · simp only [hN, hp, Nat.clog_zero_right, pow_zero]; omega
    · have := FastDet.two_pow_clog_le p hp; omega
  have hm1 : (1 : ℝ) ≤ ((p + q + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos _
  have hm0 : (0 : ℝ) ≤ ((p + q + 1 : ℕ) : ℝ) := by positivity
  -- the inversion
  have e1 : (alg.bound N : ℝ) ≤ C * 2 ^ ω * ((p + q + 1 : ℕ) : ℝ) ^ ω := by
    have h := hexp N hN1
    have h2 : ((N : ℕ) : ℝ) ≤ 2 * ((p + q + 1 : ℕ) : ℝ) := by exact_mod_cast hN2
    have h3 : ((N : ℕ) : ℝ) ^ ω ≤ (2 * ((p + q + 1 : ℕ) : ℝ)) ^ ω :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) h2 (by linarith)
    rw [Real.mul_rpow zero_le_two hm0] at h3
    calc (alg.bound N : ℝ) ≤ C * (N : ℝ) ^ ω := h
      _ ≤ C * (2 ^ ω * ((p + q + 1 : ℕ) : ℝ) ^ ω) := by gcongr
      _ = _ := by ring
  -- the two products
  have e2 : (alg.bound (p + q) : ℝ) ≤ C * ((p + q + 1 : ℕ) : ℝ) ^ ω := by
    have h := hexp (p + q + 1) (Nat.succ_pos _)
    have : alg.bound (p + q) ≤ alg.bound (p + q + 1) := alg.bound_mono (Nat.le_succ _)
    calc (alg.bound (p + q) : ℝ) ≤ alg.bound (p + q + 1) := by exact_mod_cast this
      _ ≤ _ := h
  -- the entrywise operations
  have e3 : (((p + q) * (p + q) : ℕ) : ℝ) + 1 ≤ ((p + q + 1 : ℕ) : ℝ) ^ ω := by
    have h := Real.rpow_le_rpow_of_exponent_le hm1 hω
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at h
    have : (((p + q) * (p + q) : ℕ) : ℝ) + 1 ≤ ((p + q + 1 : ℕ) : ℝ) ^ 2 := by
      push_cast; nlinarith
    linarith
  have hcb' : (BlockInverse.costBound alg (Nat.clog 2 p) : ℝ) ≤ 5 * alg.bound N := by
    have : BlockInverse.costBound alg (Nat.clog 2 p) ≤ 5 * alg.bound N := by omega
    exact_mod_cast this
  simp only [frontCost]
  push_cast
  have hpos : (0 : ℝ) ≤ ((p + q + 1 : ℕ) : ℝ) ^ ω := Real.rpow_nonneg hm0 _
  push_cast at e1 e2 e3 hpos ⊢
  nlinarith

/-- `√m ^ ω = m ^ (ω / 2)`. -/
theorem sqrt_rpow (m : ℝ) (hm : 0 ≤ m) (ω : ℝ) : √m ^ ω = m ^ (ω / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hm]
  ring_nf

omit [Fintype V] in
/-- **Geometric decrease along a shrinking tree**: for `γ > 1`,
`∑ over nodes m ^ γ ≤ n ^ γ / (1 - (2/3) ^ (γ - 1))`. -/
theorem sumNodes_rpow_le {G : SimpleGraph V} {γ : ℝ} (hγ : 1 < γ) {t : SepTree V}
    (hd : IsDissection G t) (hs : AllNodes Shrinks t) :
    sumNodes (fun u => (u.verts.card : ℝ) ^ γ) t ≤
      (t.verts.card : ℝ) ^ γ / (1 - (2 / 3 : ℝ) ^ (γ - 1)) := by
  set ρ : ℝ := (2 / 3 : ℝ) ^ (γ - 1) with hρ
  have hρ0 : 0 ≤ ρ := Real.rpow_nonneg (by norm_num) _
  have hρ1 : ρ < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) (by linarith)
  have hc : 0 < 1 - ρ := by linarith
  induction t with
  | leaf s =>
    simp only [sumNodes]
    rw [le_div_iff₀ hc]
    have : 0 ≤ ((leaf s).verts.card : ℝ) ^ γ := Real.rpow_nonneg (Nat.cast_nonneg _) _
    nlinarith
  | node s a b iha ihb =>
    simp only [sumNodes]
    have ha := iha hd.2.2.2.2.1 hs.2.1
    have hb := ihb hd.2.2.2.2.2 hs.2.2
    have hab : (a.verts.card : ℝ) + b.verts.card ≤ (node s a b).verts.card := by
      exact_mod_cast card_verts_node_le hd
    set m : ℝ := ((node s a b).verts.card : ℝ) with hm_def
    have hm : 0 ≤ m := Nat.cast_nonneg _
    -- `x ^ γ ≤ x * ρ * m ^ (γ - 1)` for the parts
    have key : ∀ x : ℕ, 3 * x ≤ 2 * (node s a b).verts.card →
        (x : ℝ) ^ γ ≤ x * (ρ * m ^ (γ - 1)) := by
      intro x hx
      have hx0 : (0 : ℝ) ≤ x := Nat.cast_nonneg _
      have hx' : (x : ℝ) ≤ 2 / 3 * m := by
        have : (3 : ℝ) * x ≤ 2 * m := by rw [hm_def]; exact_mod_cast hx
        linarith
      have e : (x : ℝ) ^ γ = x * (x : ℝ) ^ (γ - 1) := by
        rw [← Real.rpow_one_add' hx0 (by linarith)]
        · ring_nf
      rw [e, hρ, ← Real.mul_rpow (by norm_num) hm]
      gcongr
    have k1 := key _ hs.1.1
    have k2 := key _ hs.1.2
    have hmγ : m * (ρ * m ^ (γ - 1)) = ρ * m ^ γ := by
      rw [mul_left_comm, ← Real.rpow_one_add' hm (by linarith)]
      ring_nf
    have hsum : (a.verts.card : ℝ) ^ γ + (b.verts.card : ℝ) ^ γ ≤ ρ * m ^ γ := by
      have hpos : 0 ≤ ρ * m ^ (γ - 1) := mul_nonneg hρ0 (Real.rpow_nonneg hm _)
      nlinarith
    rw [le_div_iff₀ hc] at ha hb ⊢
    have hmγ0 : 0 ≤ m ^ γ := Real.rpow_nonneg hm _
    nlinarith

/-- A node with `m` vertices and separator and boundary of size at most `α √m`, `β √m` costs at
most `K₀ (α + β + 1) ^ ω m ^ (ω / 2)` operations. -/
theorem nodeCost_le (alg : MatMulAlgorithm K)
    (hreg : ∀ k, 4 * alg.bound (2 ^ k) ≤ alg.bound (2 ^ (k + 1))) (h1 : 1 ≤ alg.bound 1)
    {ω C : ℝ} (hω : 2 ≤ ω) (hexp : alg.HasExponent ω C) {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β)
    {u : SepTree V} (hu : SqrtBound G α β u) :
    (nodeCost alg G u : ℝ) ≤
      (5 * C * 2 ^ ω + 2 * C + 2) * (α + β + 1) ^ ω * (u.verts.card : ℝ) ^ (ω / 2) := by
  have hC : 0 ≤ C := by
    have := hexp 1 le_rfl
    simp only [Nat.cast_one, Real.one_rpow, mul_one] at this
    exact le_trans (Nat.cast_nonneg _) this
  have hK : 0 ≤ 5 * C * 2 ^ ω + 2 * C + 2 := by
    have : (0 : ℝ) ≤ 2 ^ ω := Real.rpow_nonneg zero_le_two _
    positivity
  unfold nodeCost
  split_ifs with hv
  · simp only [Nat.cast_zero]
    have : (0 : ℝ) ≤ (α + β + 1) ^ ω := Real.rpow_nonneg (by linarith) _
    have : (0 : ℝ) ≤ (u.verts.card : ℝ) ^ (ω / 2) := Real.rpow_nonneg (Nat.cast_nonneg _) _
    positivity
  have hN : (1 : ℝ) ≤ u.verts.card := by
    exact_mod_cast Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hv)
  have hsq : (1 : ℝ) ≤ √(u.verts.card : ℝ) := Real.one_le_sqrt.mpr hN
  have hm : (((u.own.card + (bdry G u.verts).card + 1 : ℕ)) : ℝ) ≤
      (α + β + 1) * √(u.verts.card : ℝ) := by
    obtain ⟨h₁, h₂⟩ := hu
    push_cast
    nlinarith
  have hpow : (((u.own.card + (bdry G u.verts).card + 1 : ℕ)) : ℝ) ^ ω ≤
      (α + β + 1) ^ ω * (u.verts.card : ℝ) ^ (ω / 2) := by
    calc _ ≤ ((α + β + 1) * √(u.verts.card : ℝ)) ^ ω :=
          Real.rpow_le_rpow (Nat.cast_nonneg _) hm (by linarith)
      _ = _ := by
        rw [Real.mul_rpow (by linarith) (Real.sqrt_nonneg _),
          sqrt_rpow _ (Nat.cast_nonneg _)]
  calc (frontCost alg u.own.card (bdry G u.verts).card : ℝ)
      ≤ (5 * C * 2 ^ ω + 2 * C + 2) *
          (((u.own.card + (bdry G u.verts).card + 1 : ℕ)) : ℝ) ^ ω :=
        frontCost_le alg hreg h1 hω hexp _ _
    _ ≤ (5 * C * 2 ^ ω + 2 * C + 2) * ((α + β + 1) ^ ω * (u.verts.card : ℝ) ^ (ω / 2)) := by
        gcongr
    _ = _ := by ring

/-- **Operation count of block elimination along a separator tree with fast multiplication.**
Let `t` be a separator tree of `G` covering all `n` vertices, with separators and boundaries of
size at most `α √m` and `β √m` and parts of size at most `2 m / 3` at every node with `m`
vertices.  For a multiplication algorithm with exponent `ω > 2` and constant `C` (and the
regularity condition `4 M (2 ^ k) ≤ M (2 ^ (k + 1))`, `1 ≤ M 1`), block elimination along `t`
of any matrix `A` takes at most `K₀ (α + β + 1) ^ ω / (1 - (2/3) ^ (ω/2 - 1)) * n ^ (ω / 2)`
operations, where `K₀ = 5 C 2 ^ ω + 2 C + 2`. -/
theorem ndCounted_cost_le_rpow (alg : MatMulAlgorithm K)
    (hreg : ∀ k, 4 * alg.bound (2 ^ k) ≤ alg.bound (2 ^ (k + 1))) (h1 : 1 ≤ alg.bound 1)
    {ω C : ℝ} (hω : 2 < ω) (hexp : alg.HasExponent ω C) {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (t : SepTree V) (hd : IsDissection G t) (hv : t.verts = Finset.univ)
    (hsq : AllNodes (SqrtBound G α β) t) (hs : AllNodes Shrinks t) (A : Matrix V V K) :
    ((ndCounted G alg A t).cost.total : ℝ) ≤
      (5 * C * 2 ^ ω + 2 * C + 2) * (α + β + 1) ^ ω / (1 - (2 / 3 : ℝ) ^ (ω / 2 - 1)) *
        (Fintype.card V : ℝ) ^ (ω / 2) := by
  set K₁ := (5 * C * 2 ^ ω + 2 * C + 2) * (α + β + 1) ^ ω
  have hK₁ : 0 ≤ K₁ := by
    have hC : 0 ≤ C := by
      have := hexp 1 le_rfl
      simp only [Nat.cast_one, Real.one_rpow, mul_one] at this
      exact le_trans (Nat.cast_nonneg _) this
    have : (0 : ℝ) ≤ 2 ^ ω := Real.rpow_nonneg zero_le_two _
    have : (0 : ℝ) ≤ (α + β + 1) ^ ω := Real.rpow_nonneg (by linarith) _
    positivity
  have h₁ : ((ndCounted G alg A t).cost.total : ℝ) ≤
      sumNodes (fun u => (nodeCost alg G u : ℝ)) t := by
    rw [← sumNodes_cast]
    exact_mod_cast ndCounted_cost_le alg A t
  have h₂ : sumNodes (fun u => (nodeCost alg G u : ℝ)) t ≤
      sumNodes (fun u => K₁ * (u.verts.card : ℝ) ^ (ω / 2)) t :=
    sumNodes_le_of_allNodes (fun u hu => nodeCost_le alg hreg h1 hω.le hexp hα hβ hu) hsq
  have h₃ := sumNodes_rpow_le (γ := ω / 2) (by linarith) hd hs
  rw [sumNodes_mul_left] at h₂
  rw [hv, Finset.card_univ] at h₃
  calc ((ndCounted G alg A t).cost.total : ℝ)
      ≤ K₁ * sumNodes (fun u => (u.verts.card : ℝ) ^ (ω / 2)) t :=
        h₁.trans h₂
    _ ≤ K₁ * ((Fintype.card V : ℝ) ^ (ω / 2) / (1 - (2 / 3 : ℝ) ^ (ω / 2 - 1))) := by gcongr
    _ = _ := by ring

/-- **Nested dissection with fast matrix multiplication.**  Let `t` be a separator tree of `G`
covering all `n` vertices, with separators and boundaries of size at most `α √m` and `β √m` and
parts of size at most `2 m / 3` at every node with `m` vertices, and let `A` have its
off-diagonal nonzero entries on edges of `G` and satisfy the regularity hypothesis.  For a
multiplication algorithm with exponent `ω > 2` and constant `C` (and the regularity condition
`4 M (2 ^ k) ≤ M (2 ^ (k + 1))`, `1 ≤ M 1`), block elimination along `t` computes `det A` with
at most `K₀ (α + β + 1) ^ ω / (1 - (2/3) ^ (ω/2 - 1)) * n ^ (ω / 2)` operations, where
`K₀ = 5 C 2 ^ ω + 2 C + 2`. -/
theorem nestedDissection_fast (alg : MatMulAlgorithm K)
    (hreg : ∀ k, 4 * alg.bound (2 ^ k) ≤ alg.bound (2 ^ (k + 1))) (h1 : 1 ≤ alg.bound 1)
    {ω C : ℝ} (hω : 2 < ω) (hexp : alg.HasExponent ω C) {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (t : SepTree V) (hd : IsDissection G t) (hv : t.verts = Finset.univ)
    (hsq : AllNodes (SqrtBound G α β) t) (hs : AllNodes Shrinks t)
    (A : Matrix V V K) (hA : ∀ x y, x ≠ y → A x y ≠ 0 → G.Adj x y)
    (hr : AllNodes (NodeRegular A) t) :
    (ndCounted G alg A t).val.1 = A.det ∧
      ((ndCounted G alg A t).cost.total : ℝ) ≤
        (5 * C * 2 ^ ω + 2 * C + 2) * (α + β + 1) ^ ω / (1 - (2 / 3 : ℝ) ^ (ω / 2 - 1)) *
          (Fintype.card V : ℝ) ^ (ω / 2) := by
  refine ⟨?_, ndCounted_cost_le_rpow alg hreg h1 hω hexp hα hβ t hd hv hsq hs A⟩
  rw [(ndCounted_val alg hA t hd hr).1, hv]
  exact det_submatrix_equiv_self (Equiv.subtypeUnivEquiv Finset.mem_univ) A

theorem two_lt_strassenExponent : 2 < Strassen.strassenExponent := by
  rw [Strassen.strassenExponent, Real.lt_logb_iff_rpow_lt one_lt_two (by norm_num)]
  norm_num

/-- **Nested dissection with Strassen's algorithm**: `O(n ^ (log₂ 7 / 2)) = O(n ^ 1.41)`
operations. -/
theorem nestedDissection_strassen {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (t : SepTree V) (hd : IsDissection G t) (hv : t.verts = Finset.univ)
    (hsq : AllNodes (SqrtBound G α β) t) (hs : AllNodes Shrinks t)
    (A : Matrix V V K) (hA : ∀ x y, x ≠ y → A x y ≠ 0 → G.Adj x y)
    (hr : AllNodes (NodeRegular A) t) :
    (ndCounted G (MatMulAlgorithm.strassen K) A t).val.1 = A.det ∧
      ((ndCounted G (MatMulAlgorithm.strassen K) A t).cost.total : ℝ) ≤
        (5 * 49 * 2 ^ Strassen.strassenExponent + 2 * 49 + 2) *
          (α + β + 1) ^ Strassen.strassenExponent /
          (1 - (2 / 3 : ℝ) ^ (Strassen.strassenExponent / 2 - 1)) *
          (Fintype.card V : ℝ) ^ (Strassen.strassenExponent / 2) :=
  nestedDissection_fast _ FastDet.strassen_regular FastDet.strassen_bound_one
    two_lt_strassenExponent (MatMulAlgorithm.strassen_hasExponent K) hα hβ t hd hv hsq hs A hA hr

/-! ### Regularity in the nested dissection order -/

omit [Fintype V] in
theorem initSeg_eq_take (s : Finset V) (j : ℕ) :
    initSeg s j = ((s.sort (· ≤ ·)).take j).toFinset := by
  ext x
  rw [mem_initSeg, List.mem_toFinset, List.mem_take_iff_getElem]
  constructor
  · rintro ⟨i, hi, rfl⟩
    refine ⟨i, ?_, ?_⟩
    · rw [Finset.length_sort]; exact lt_min hi i.2
    · simp [pt, Finset.orderEmbOfFin_apply]
  · rintro ⟨i, hi, rfl⟩
    rw [Finset.length_sort] at hi
    refine ⟨⟨i, (lt_min_iff.mp hi).2⟩, (lt_min_iff.mp hi).1, ?_⟩
    simp [pt, Finset.orderEmbOfFin_apply]

omit [Fintype V] in
/-- Block diagonal determinant: no coupling between `X` and `Y`. -/
theorem det_union_of_zero (A : Matrix V V K) {X Y : Finset V} (h : Disjoint X Y)
    (hXY : ∀ u ∈ X, ∀ v ∈ Y, A u v = 0 ∧ A v u = 0) :
    (principal A (X ∪ Y)).det = (principal A X).det * (principal A Y).det := by
  set e := Equiv.Finset.union X Y h
  have hb : (principal A (X ∪ Y)).submatrix e e = fromBlocks (principal A X) 0 0
      (principal A Y) := by
    ext (a | a) (b | b)
    · rfl
    · exact (hXY a a.2 b b.2).1
    · exact (hXY b b.2 a a.2).2
    · rfl
  rw [← det_submatrix_equiv_self e, hb, det_fromBlocks_zero₁₂]

omit [Fintype V] in
/-- The regularity hypothesis at the root of a subtree from the principal minors on the initial
segments of an elimination order containing the order of the subtree as a contiguous block. -/
theorem nodeRegular_of_take {A : Matrix V V K} (L : List V) (hnd : L.Nodup)
    (hL : ∀ k ≤ L.length, (principal A (L.take k).toFinset).det ≠ 0)
    {t : SepTree V} (PL : List V) (hPL : t.order = PL ++ t.own.sort (· ≤ ·))
    (hPV : partVerts t = PL.toFinset) (Pre Post : List V) (hL' : L = Pre ++ t.order ++ Post)
    (hPre : ∀ x ∈ Pre, ∀ y ∈ t.verts, A x y = 0 ∧ A y x = 0) : NodeRegular A t := by
  intro j hj
  have hjs : j ≤ (t.own.sort (· ≤ ·)).length := by rwa [Finset.length_sort]
  have htake : L.take ((Pre ++ PL).length + j) = Pre ++ PL ++ (t.own.sort (· ≤ ·)).take j := by
    rw [hL', hPL, show Pre ++ (PL ++ t.own.sort (· ≤ ·)) ++ Post =
      (Pre ++ PL) ++ (t.own.sort (· ≤ ·) ++ Post) by simp, List.take_length_add_append,
      List.take_append_of_le_length hjs]
  have hk : (Pre ++ PL).length + j ≤ L.length := by
    rw [hL', hPL]; simp only [List.length_append]; omega
  have hQ : partVerts t ∪ initSeg t.own j ⊆ t.verts := by
    rw [← partVerts_union_own]
    exact Finset.union_subset_union le_rfl (initSeg_subset _ _)
  have hset : (L.take ((Pre ++ PL).length + j)).toFinset =
      Pre.toFinset ∪ (partVerts t ∪ initSeg t.own j) := by
    rw [htake, hPV, initSeg_eq_take]
    ext x; simp
  have hdisj : Disjoint Pre.toFinset (partVerts t ∪ initSeg t.own j) := by
    rw [Finset.disjoint_left]
    intro x hx hxQ
    have hnd' : (Pre ++ t.order).Nodup := by
      rw [hL'] at hnd; exact hnd.sublist (List.sublist_append_left _ _)
    exact List.disjoint_of_nodup_append hnd' (List.mem_toFinset.mp hx)
      (mem_order.mpr (hQ hxQ))
  have := hL _ hk
  rw [hset, det_union_of_zero A hdisj (fun u hu v hv => hPre u (List.mem_toFinset.mp hu) v
    (hQ hv))] at this
  exact right_ne_zero_of_mul this

omit [Fintype V] [DecidableRel G.Adj] in
/-- The regularity hypothesis at all nodes from the principal minors on the initial segments of
an elimination order containing the order of the tree as a contiguous block, preceded only by
vertices not coupled to the tree. -/
theorem allNodes_nodeRegular_of_take {A : Matrix V V K}
    (hA : ∀ x y, x ≠ y → A x y ≠ 0 → G.Adj x y) (L : List V) (hnd : L.Nodup)
    (hL : ∀ k ≤ L.length, (principal A (L.take k).toFinset).det ≠ 0) :
    ∀ (t : SepTree V), IsDissection G t → ∀ (Pre Post : List V), L = Pre ++ t.order ++ Post →
      (∀ x ∈ Pre, ∀ y ∈ t.verts, A x y = 0 ∧ A y x = 0) → AllNodes (NodeRegular A) t
  | leaf s, _, Pre, Post, hL', hPre =>
    nodeRegular_of_take L hnd hL [] (by simp [order, own]) (by simp [partVerts]) Pre Post hL' hPre
  | node s a b, hd, Pre, Post, hL', hPre => by
    refine ⟨nodeRegular_of_take L hnd hL (a.order ++ b.order) (by simp [order, own])
      (by ext x; simp [partVerts, mem_order]) Pre Post hL' hPre, ?_, ?_⟩
    · refine allNodes_nodeRegular_of_take hA L hnd hL a hd.2.2.2.2.1 Pre
        (b.order ++ s.sort (· ≤ ·) ++ Post) (by rw [hL']; simp [order]) fun x hx y hy => ?_
      exact hPre x hx y (by simp [verts, hy])
    · refine allNodes_nodeRegular_of_take hA L hnd hL b hd.2.2.2.2.2 (Pre ++ a.order)
        (s.sort (· ≤ ·) ++ Post) (by rw [hL']; simp [order]) fun x hx y hy => ?_
      rcases List.mem_append.mp hx with hx | hx
      · exact hPre x hx y (by simp [verts, hy])
      · rw [mem_order] at hx
        have hne : x ≠ y := fun h => Finset.disjoint_left.mp hd.2.2.1 hx (h ▸ hy)
        refine ⟨by_contra fun h => hd.2.2.2.1 x hx y hy (hA x y hne h), by_contra fun h => ?_⟩
        exact hd.2.2.2.1 x hx y hy (hA y x hne.symm h).symm

section Fin

variable {n : ℕ} {G : SimpleGraph (Fin n)}

theorem length_order {t : SepTree (Fin n)} (hd : IsDissection G t) (hv : t.verts = Finset.univ) :
    t.order.length = n := by
  rw [← List.toFinset_card_of_nodup (nodup_order hd)]
  have : t.order.toFinset = Finset.univ := by
    ext x; simp [mem_order, hv]
  rw [this, Finset.card_univ, Fintype.card_fin]

/-- The leading principal minors in the nested dissection order are the principal minors on the
initial segments of the order. -/
theorem det_leading_ndPerm {t : SepTree (Fin n)} (hd : IsDissection G t)
    (hv : t.verts = Finset.univ) (A : Matrix (Fin n) (Fin n) K) (k : ℕ) (hk : k ≤ n) :
    (leading (A.submatrix (ndPerm t hd hv) (ndPerm t hd hv)) k hk).det =
      (principal A (t.order.take k).toFinset).det := by
  have hlen := length_order hd hv
  have hmem : ∀ i : Fin k, ndPerm t hd hv (Fin.castLE hk i) ∈ (t.order.take k).toFinset := by
    intro i
    rw [List.mem_toFinset, List.mem_take_iff_getElem]
    exact ⟨i, lt_min i.2 (by omega), rfl⟩
  let e : Fin k ≃ (t.order.take k).toFinset := Equiv.ofBijective
    (fun i => ⟨ndPerm t hd hv (Fin.castLE hk i), hmem i⟩) <| by
      refine ⟨fun i j h => Fin.castLE_injective hk ((ndPerm t hd hv).injective
        (congrArg Subtype.val h)), ?_⟩
      rintro ⟨x, hx⟩
      rw [List.mem_toFinset, List.mem_take_iff_getElem] at hx
      obtain ⟨j, hj, rfl⟩ := hx
      exact ⟨⟨j, (lt_min_iff.mp hj).1⟩, rfl⟩
  have : leading (A.submatrix (ndPerm t hd hv) (ndPerm t hd hv)) k hk =
      (principal A (t.order.take k).toFinset).submatrix e e := rfl
  rw [this, det_submatrix_equiv_self]

/-- **Regularity from nonzero leading principal minors in the nested dissection order.** -/
theorem allNodes_nodeRegular_of_leading {t : SepTree (Fin n)} (hd : IsDissection G t)
    (hv : t.verts = Finset.univ) {A : Matrix (Fin n) (Fin n) K}
    (hA : ∀ x y, x ≠ y → A x y ≠ 0 → G.Adj x y)
    (h : ∀ k (hk : k ≤ n), (leading (A.submatrix (ndPerm t hd hv) (ndPerm t hd hv)) k hk).det ≠ 0) :
    AllNodes (NodeRegular A) t := by
  refine allNodes_nodeRegular_of_take hA t.order (nodup_order hd) (fun k hk => ?_) t hd [] []
    (by simp) (by simp)
  rw [length_order hd hv] at hk
  rw [← det_leading_ndPerm hd hv A k hk]
  exact h k hk

/-- **Regularity from nonzero pivots in the nested dissection order.** -/
theorem allNodes_nodeRegular_of_pivotsIn {t : SepTree (Fin n)} (hd : IsDissection G t)
    (hv : t.verts = Finset.univ) {A : Matrix (Fin n) (Fin n) K}
    (hA : ∀ x y, x ≠ y → A x y ≠ 0 → G.Adj x y)
    (h : ∀ k : Fin n, pivotsIn (ndPerm t hd hv) A k ≠ 0) :
    AllNodes (NodeRegular A) t := by
  refine allNodes_nodeRegular_of_leading hd hv hA fun k hk => ?_
  rw [det_leading_eq_prod_pivots _ k hk fun j _ => h j]
  exact Finset.prod_ne_zero_iff.mpr fun j _ => h _

/-- **Nested dissection with fast matrix multiplication, in the nested dissection order.**
Under the hypotheses of `nestedDissection_fast` on the tree and the multiplication algorithm, if
all pivots of elimination in the nested dissection order are nonzero, block elimination along the
tree computes `det A` with `O(n ^ (ω / 2))` operations. -/
theorem nestedDissection_fast_of_pivotsIn [DecidableRel G.Adj] (alg : MatMulAlgorithm K)
    (hreg : ∀ k, 4 * alg.bound (2 ^ k) ≤ alg.bound (2 ^ (k + 1))) (h1 : 1 ≤ alg.bound 1)
    {ω C : ℝ} (hω : 2 < ω) (hexp : alg.HasExponent ω C) {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (t : SepTree (Fin n)) (hd : IsDissection G t) (hv : t.verts = Finset.univ)
    (hsq : AllNodes (SqrtBound G α β) t) (hs : AllNodes Shrinks t)
    (A : Matrix (Fin n) (Fin n) K) (hA : ∀ x y, x ≠ y → A x y ≠ 0 → G.Adj x y)
    (hpiv : ∀ k : Fin n, pivotsIn (ndPerm t hd hv) A k ≠ 0) :
    (ndCounted G alg A t).val.1 = A.det ∧
      ((ndCounted G alg A t).cost.total : ℝ) ≤
        (5 * C * 2 ^ ω + 2 * C + 2) * (α + β + 1) ^ ω / (1 - (2 / 3 : ℝ) ^ (ω / 2 - 1)) *
          (n : ℝ) ^ (ω / 2) := by
  simpa using nestedDissection_fast alg hreg h1 hω hexp hα hβ t hd hv hsq hs A hA
    (allNodes_nodeRegular_of_pivotsIn hd hv hA hpiv)

end Fin

end FastDissection

end

end FastGE
