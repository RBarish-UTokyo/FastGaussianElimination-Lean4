module

public import FastGE.FastDet
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.Data.Finset.Sort

/-!
# Schur complements on vertex sets and the frontal step

`principal`, `rectMul`, `frontStep` and the enumeration of a finset (`pt`, `idx`,
`initSeg`) are defined in `FastGE/Spec.lean`.

For a matrix `A : Matrix V V K` indexed by a finite type `V` and a set `W ⊆ V` with invertible
principal submatrix `A[W, W]` (`principal A W`), the *correction*
```
  corr A W = A[:, W] A[W, W]⁻¹ A[W, :]
```
is an `V × V` matrix; on the positions outside `W`, `A - corr A W` is the Schur complement of
`A[W, W]`.  This file collects the facts about Schur complements used by block elimination along
a separator tree [R. J. Lipton, D. J. Rose, R. E. Tarjan, *Generalized nested dissection*, SIAM
J. Numer. Anal. 16 (1979), 346–358; V. Pan, J. Reif, *Fast and efficient parallel solution of
sparse linear systems*, SIAM J. Comput. 22 (1993), 1227–1250]:

* `det_union`: `det A[X ∪ Y] = det A[X] * det (A - corr A X)[Y]` (Schur's determinant formula);
* `corr_union`: the quotient property `corr A (X ∪ Y) = corr A X + corr (A - corr A X) Y`;
* `corr_union_of_zero`: if `A` has no entries between `X` and `Y`, the corrections and the
  determinants of `X` and `Y` simply add up, respectively multiply;
* `corr_apply_eq_zero_of_row`, `corr_apply_eq_zero_of_col`: sparsity of the correction.

The *frontal step* `frontStep` takes the corrections `Fa`, `Fb` already computed for the two parts
of a node of a separator tree, eliminates the separator `s` of the node with the dense block
inversion of `FastGE.FastDet` and two products of size `|s| + |Bd|` (computed by
`rectMul`, a rectangular product padded with zeros), and returns the correction of the whole
vertex set of the node on its boundary `Bd`, together with the determinant of the principal
submatrix (`frontStep_val`).  Its operation count is `frontCost alg |s| |Bd|`
(`frontStep_cost_le`).
-/

namespace FastGE

open WordRAM.Algebraic Matrix

@[expose] public section

universe u

namespace Frontal

section Schur

variable {V : Type} [DecidableEq V] {K : Type u} [Field K]

/-- The correction `A[:, W] A[W, W]⁻¹ A[W, :]`; outside `W`, `A - corr A W` is the Schur
complement of `A[W, W]`. -/
noncomputable def corr (A : Matrix V V K) (W : Finset V) : Matrix V V K :=
  A.submatrix id ((↑) : W → V) * (principal A W)⁻¹ * A.submatrix ((↑) : W → V) id

theorem corr_def (A : Matrix V V K) (W : Finset V) : corr A W =
    A.submatrix id ((↑) : W → V) * (principal A W)⁻¹ * A.submatrix ((↑) : W → V) id := rfl

theorem corr_apply (A : Matrix V V K) (W : Finset V) (x y : V) :
    corr A W x y = ∑ v : W, (∑ u : W, A x u * (principal A W)⁻¹ u v) * A v y := by
  simp [corr, Matrix.mul_apply]

/-- Rows of `A` vanishing on `W` give vanishing rows of the correction. -/
theorem corr_apply_eq_zero_of_row (A : Matrix V V K) (W : Finset V) {x : V}
    (hx : ∀ u ∈ W, A x u = 0) (y : V) : corr A W x y = 0 := by
  simp [corr_apply, hx]

/-- Columns of `A` vanishing on `W` give vanishing columns of the correction. -/
theorem corr_apply_eq_zero_of_col (A : Matrix V V K) (W : Finset V) {y : V}
    (hy : ∀ u ∈ W, A u y = 0) (x : V) : corr A W x y = 0 := by
  simp [corr_apply, hy]

@[simp] theorem corr_empty (A : Matrix V V K) : corr A ∅ = 0 := by
  ext x y; simp [corr_apply]

@[simp] theorem det_principal_empty (A : Matrix V V K) : (principal A ∅).det = 1 := det_isEmpty

theorem principal_sub_corr (A : Matrix V V K) (X Y : Finset V) :
    principal (A - corr A X) Y =
      principal A Y - A.submatrix ((↑) : Y → V) ((↑) : X → V) * (principal A X)⁻¹ *
        A.submatrix ((↑) : X → V) ((↑) : Y → V) := by
  ext u v
  simp [corr, Matrix.mul_apply]

/-- **Schur's determinant formula** for disjoint vertex sets. -/
theorem det_union (A : Matrix V V K) {X Y : Finset V} (h : Disjoint X Y)
    (hX : (principal A X).det ≠ 0) :
    (principal A (X ∪ Y)).det = (principal A X).det * (principal (A - corr A X) Y).det := by
  set e := Equiv.Finset.union X Y h
  have hb : (principal A (X ∪ Y)).submatrix e e = fromBlocks (principal A X)
      (A.submatrix ((↑) : X → V) ((↑) : Y → V)) (A.submatrix ((↑) : Y → V) ((↑) : X → V))
      (principal A Y) := by
    ext (a | a) (b | b) <;> rfl
  rw [← det_submatrix_equiv_self e, hb, BlockInverse.det_fromBlocks _ _ _ _ hX, principal_sub_corr]

/-- The correction computed in any enumeration of `W`. -/
theorem corr_reindex {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix V V K) (W : Finset V)
    (e : ι ≃ W) :
    corr A W = A.submatrix id (fun i => (e i : V)) * ((principal A W).submatrix e e)⁻¹ *
      A.submatrix (fun i => (e i : V)) id := by
  rw [inv_submatrix_equiv, corr]
  have h1 : A.submatrix id (fun i => (e i : V)) =
      (A.submatrix id ((↑) : W → V)).submatrix id e := rfl
  have h2 : A.submatrix (fun i => (e i : V)) id =
      (A.submatrix ((↑) : W → V) id).submatrix e id := rfl
  rw [h1, h2, submatrix_mul_equiv, submatrix_mul_equiv]
  simp

theorem submatrix_sub_corr {ι κ : Type*} (A : Matrix V V K) (X : Finset V) (f : ι → V)
    (g : κ → V) :
    (A - corr A X).submatrix f g = A.submatrix f g -
      A.submatrix f ((↑) : X → V) * (principal A X)⁻¹ * A.submatrix ((↑) : X → V) g := by
  ext u v
  simp [corr, Matrix.mul_apply]

/-- **Quotient property** of Schur complements: eliminating `X ∪ Y` is eliminating `X`, then
`Y` in the Schur complement. -/
theorem corr_union (A : Matrix V V K) {X Y : Finset V} (h : Disjoint X Y)
    (hX : (principal A X).det ≠ 0) (hY : (principal (A - corr A X) Y).det ≠ 0) :
    corr A (X ∪ Y) = corr A X + corr (A - corr A X) Y := by
  set e := Equiv.Finset.union X Y h
  have hb : (principal A (X ∪ Y)).submatrix e e = fromBlocks (principal A X)
      (A.submatrix ((↑) : X → V) ((↑) : Y → V)) (A.submatrix ((↑) : Y → V) ((↑) : X → V))
      (principal A Y) := by
    ext (a | a) (b | b) <;> rfl
  have hc : A.submatrix id (fun i => (e i : V)) =
      fromCols (A.submatrix id ((↑) : X → V)) (A.submatrix id ((↑) : Y → V)) := by
    ext a (b | b) <;> rfl
  have hr : A.submatrix (fun i => (e i : V)) id =
      fromRows (A.submatrix ((↑) : X → V) id) (A.submatrix ((↑) : Y → V) id) := by
    ext (a | a) b <;> rfl
  have hY' := hY
  rw [principal_sub_corr] at hY'
  rw [corr_reindex A _ e, hb, hc, hr, BlockInverse.inv_fromBlocks _ _ _ _ hX hY',
    fromCols_mul_fromBlocks, fromCols_mul_fromRows]
  conv_rhs => rw [corr_def (A - corr A X) Y, principal, submatrix_sub_corr, submatrix_sub_corr,
    submatrix_sub_corr, corr]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_neg,
    Matrix.neg_mul, Matrix.mul_assoc]
  abel

/-- The correction of `W` depends only on the rows and columns of `W`. -/
theorem corr_congr {A B : Matrix V V K} {W : Finset V}
    (h : ∀ x, ∀ v ∈ W, B x v = A x v ∧ B v x = A v x) : corr B W = corr A W := by
  have h1 : B.submatrix id ((↑) : W → V) = A.submatrix id ((↑) : W → V) := by
    ext x v; exact (h x v v.2).1
  have h2 : B.submatrix ((↑) : W → V) id = A.submatrix ((↑) : W → V) id := by
    ext v x; exact (h x v v.2).2
  have h3 : principal B W = principal A W := by
    ext u v; exact (h u v v.2).1
  rw [corr_def, corr_def, h1, h2, h3]

theorem corr_sub_apply_of_zero (A : Matrix V V K) {X Y : Finset V}
    (hXY : ∀ u ∈ X, ∀ v ∈ Y, A u v = 0 ∧ A v u = 0) :
    ∀ x, ∀ v ∈ Y, (A - corr A X) x v = A x v ∧ (A - corr A X) v x = A v x := by
  intro x v hv
  refine ⟨?_, ?_⟩
  · rw [Matrix.sub_apply, corr_apply_eq_zero_of_col A X (fun u hu => (hXY u hu v hv).1), sub_zero]
  · rw [Matrix.sub_apply, corr_apply_eq_zero_of_row A X (fun u hu => (hXY u hu v hv).2), sub_zero]

/-- Block diagonal case: no coupling between `X` and `Y`. -/
theorem corr_union_of_zero (A : Matrix V V K) {X Y : Finset V} (h : Disjoint X Y)
    (hXY : ∀ u ∈ X, ∀ v ∈ Y, A u v = 0 ∧ A v u = 0) (hX : (principal A X).det ≠ 0)
    (hY : (principal A Y).det ≠ 0) :
    corr A (X ∪ Y) = corr A X + corr A Y ∧
      (principal A (X ∪ Y)).det = (principal A X).det * (principal A Y).det := by
  have hc := corr_sub_apply_of_zero A hXY
  have hs : principal (A - corr A X) Y = principal A Y := by
    ext u v; exact (hc u v v.2).1
  rw [corr_union A h hX (hs ▸ hY), det_union A h hX, hs, corr_congr hc]
  exact ⟨rfl, rfl⟩

end Schur

section RectMul

variable {K : Type u} [Field K]

/-- The product of embedded matrices contains the product of the original matrices. -/
theorem extract_embed_mul {m p q r : ℕ} (hp : p ≤ m) (hq : q ≤ m) (hr : r ≤ m)
    (A : Matrix (Fin p) (Fin q) K) (B : Matrix (Fin q) (Fin r) K) :
    (embed m A * embed m B).submatrix (Fin.castLE hp) (Fin.castLE hr) = A * B := by
  ext i j
  simp only [submatrix_apply, Matrix.mul_apply, embed, of_apply, Fin.val_castLE]
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.map (Fin.castLEEmb hq)))]
  · rw [Finset.sum_map]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp [i.2, j.2, l.2]
  · intro l _ hl
    have : q ≤ (l : ℕ) := by
      by_contra hlt
      exact hl (Finset.mem_map.mpr ⟨⟨l, by omega⟩, Finset.mem_univ _, Fin.ext rfl⟩)
    simp [show ¬ (l : ℕ) < q by omega]


theorem rectMul_val (alg : MatMulAlgorithm K) (m : ℕ) {p q r : ℕ} (hp : p ≤ m) (hq : q ≤ m)
    (hr : r ≤ m) (A : Matrix (Fin p) (Fin q) K) (B : Matrix (Fin q) (Fin r) K) :
    (rectMul alg m hp hr A B).val = A * B := by
  simp [rectMul, alg.mul_val, extract_embed_mul hp hq hr]

theorem rectMul_cost_le (alg : MatMulAlgorithm K) (m : ℕ) {p q r : ℕ} (hp : p ≤ m)
    (hr : r ≤ m) (A : Matrix (Fin p) (Fin q) K) (B : Matrix (Fin q) (Fin r) K) :
    (rectMul alg m hp hr A B).cost.total ≤ alg.bound m := by
  simpa [rectMul] using alg.cost_le m _ _


end RectMul

section Front

variable {V : Type} [LinearOrder V] {K : Type u} [Field K]

theorem pt_mem (s : Finset V) (i : Fin s.card) : pt s i ∈ s := (s.orderIsoOfFin rfl i).2

theorem pt_injective (s : Finset V) : Function.Injective (pt s) := fun _ _ h =>
  (s.orderIsoOfFin rfl).injective (Subtype.ext h)

@[simp] theorem pt_idx (s : Finset V) {x : V} (hx : x ∈ s) : pt s (idx s hx) = x := by
  simp [pt, idx]

theorem mem_initSeg {s : Finset V} {j : ℕ} {x : V} :
    x ∈ initSeg s j ↔ ∃ i : Fin s.card, (i : ℕ) < j ∧ pt s i = x := by
  simp [initSeg]

theorem initSeg_subset (s : Finset V) (j : ℕ) : initSeg s j ⊆ s := by
  intro x hx
  obtain ⟨i, -, rfl⟩ := mem_initSeg.mp hx
  exact pt_mem s i

@[simp] theorem initSeg_zero (s : Finset V) : initSeg s 0 = ∅ := by
  ext x; simp [mem_initSeg]

@[simp] theorem initSeg_card (s : Finset V) : initSeg s s.card = s := by
  refine Finset.Subset.antisymm (initSeg_subset s _) fun x hx => mem_initSeg.mpr ?_
  exact ⟨idx s hx, (idx s hx).2, pt_idx s hx⟩

/-- `Fin j` enumerates `initSeg s j`. -/
noncomputable def initSegEquiv (s : Finset V) {j : ℕ} (hj : j ≤ s.card) : Fin j ≃ initSeg s j :=
  Equiv.ofBijective (fun i => ⟨pt s (Fin.castLE hj i), mem_initSeg.mpr ⟨_, i.2, rfl⟩⟩) <| by
    refine ⟨fun a b h => Fin.castLE_injective hj
      (pt_injective s (by simpa using congrArg Subtype.val h)), ?_⟩
    rintro ⟨x, hx⟩
    obtain ⟨i, hi, rfl⟩ := mem_initSeg.mp hx
    exact ⟨⟨i, hi⟩, rfl⟩

omit [LinearOrder V] in
@[simp] theorem entry_val (A Fa Fb : Matrix V V K) (x y : V) :
    (entry A Fa Fb x y).val = A x y - Fa x y - Fb x y := rfl

omit [LinearOrder V] in
@[simp] theorem entry_cost (A Fa Fb : Matrix V V K) (x y : V) :
    (entry A Fa Fb x y).cost = ⟨2, 0⟩ := rfl

omit [LinearOrder V] in
@[simp] theorem sumUpd_val (Fa Fb : Matrix V V K) {q : ℕ} (e : Fin q → V)
    (R : Matrix (Fin q) (Fin q) K) (i j : Fin q) :
    (sumUpd Fa Fb e R).val i j = Fa (e i) (e j) + Fb (e i) (e j) + R i j := rfl

omit [LinearOrder V] in
@[simp] theorem sumUpd_cost (Fa Fb : Matrix V V K) {q : ℕ} (e : Fin q → V)
    (R : Matrix (Fin q) (Fin q) K) : (sumUpd Fa Fb e R).cost.total = 2 * (q * q) := by
  simp [sumUpd, Finset.card_univ, OpCount.total]
  ring

/-- **Correctness of the frontal step.**  Let `X` (the vertices eliminated below the node) and
`s` (its separator) be disjoint, let `Bd` be disjoint from `W = X ∪ s` and contain every vertex
outside `W` coupled to `W`, and let `Fa + Fb` be the correction of `X` and `da * db` the
determinant of `A[X, X]`.  If the principal submatrices on `X` together with an initial segment of
`s` are invertible, `frontStep` returns `det A[W, W]` and the correction of `W` outside `W`. -/
theorem frontStep_val (alg : MatMulAlgorithm K) (A Fa Fb : Matrix V V K) (da db : K)
    {X s Bd : Finset V} (hXs : Disjoint X s) (hBd : Disjoint Bd (X ∪ s))
    (hsp : ∀ x, x ∉ X ∪ s → x ∉ Bd → ∀ u ∈ X ∪ s, A x u = 0 ∧ A u x = 0)
    (hF : ∀ x y, x ∉ X → y ∉ X → Fa x y + Fb x y = corr A X x y)
    (hd : da * db = (principal A X).det)
    (hreg : ∀ j ≤ s.card, (principal A (X ∪ initSeg s j)).det ≠ 0) :
    (frontStep alg A Fa Fb da db s Bd).val.1 = (principal A (X ∪ s)).det ∧
      ∀ x y, x ∉ X ∪ s → y ∉ X ∪ s →
        (frontStep alg A Fa Fb da db s Bd).val.2 x y = corr A (X ∪ s) x y := by
  set A' := A - corr A X with hA'
  have hX0 : (principal A X).det ≠ 0 := by
    have := hreg 0 (Nat.zero_le _)
    rwa [initSeg_zero, Finset.union_empty] at this
  have hs0 : (principal A' s).det ≠ 0 := by
    have := hreg s.card le_rfl
    rw [initSeg_card, det_union A hXs hX0] at this
    exact right_ne_zero_of_mul this
  have hE : ∀ x y, x ∉ X → y ∉ X → A x y - Fa x y - Fb x y = A' x y := by
    intro x y hx hy
    rw [hA', Matrix.sub_apply, ← hF x y hx hy]
    ring
  have hsX : ∀ i, pt s i ∉ X := fun i h => Finset.disjoint_left.mp hXs h (pt_mem s i)
  have hBX : ∀ i, pt Bd i ∉ X := fun i h =>
    Finset.disjoint_left.mp hBd (pt_mem Bd i) (Finset.mem_union_left _ h)
  set eS := (s.orderIsoOfFin rfl).toEquiv with heS
  have hP : Matrix.of (fun i j => (entry A Fa Fb (pt s i) (pt s j)).val) =
      (principal A' s).submatrix eS eS := by
    ext i j
    simp only [of_apply, entry_val, hE _ _ (hsX i) (hsX j)]
    rfl
  have hB : Matrix.of (fun i j => (entry A Fa Fb (pt s i) (pt Bd j)).val) =
      A'.submatrix (pt s) (pt Bd) := by
    ext i j
    simp only [of_apply, entry_val, hE _ _ (hsX i) (hBX j)]
    rfl
  have hC : Matrix.of (fun i j => (entry A Fa Fb (pt Bd i) (pt s j)).val) =
      A'.submatrix (pt Bd) (pt s) := by
    ext i j
    simp only [of_apply, entry_val, hE _ _ (hBX i) (hsX j)]
    rfl
  have hlead : ∀ j hj,
      (NestedDissection.leading ((principal A' s).submatrix eS eS) j hj).det ≠ 0 := by
    intro j hj
    have e : NestedDissection.leading ((principal A' s).submatrix eS eS) j hj =
        (principal A' (initSeg s j)).submatrix (initSegEquiv s hj) (initSegEquiv s hj) := rfl
    rw [e, det_submatrix_equiv_self]
    have := hreg j hj
    rw [det_union A (hXs.mono_right (initSeg_subset s j)) hX0] at this
    exact right_ne_zero_of_mul this
  have hinv := FastDet.invDet_val alg _ hlead
  have hR : A'.submatrix (pt Bd) (pt s) * ((principal A' s).submatrix eS eS)⁻¹ *
      A'.submatrix (pt s) (pt Bd) = (corr A' s).submatrix (pt Bd) (pt Bd) := by
    rw [corr_reindex A' s eS]
    ext i j
    simp only [submatrix_apply, Matrix.mul_apply, id]
    rfl
  have hU := corr_union A hXs hX0 hs0
  simp only [frontStep, Counted.val_bind, Counted.val_pure, Counted.val_pi, Op.val_mul,
    sumUpd_val]
  rw [hP, hC, hB, hinv]
  simp only [rectMul_val alg _ _ (Nat.le_add_right s.card Bd.card), hR]
  refine ⟨?_, fun x y hx hy => ?_⟩
  · rw [hd, det_submatrix_equiv_self, det_union A hXs hX0]
  · simp only [of_apply]
    by_cases hxB : x ∈ Bd
    · by_cases hyB : y ∈ Bd
      · rw [dite_eq_left hxB, dite_eq_left hyB, submatrix_apply, pt_idx, pt_idx,
          hF x y (fun h => hx (Finset.mem_union_left _ h))
            (fun h => hy (Finset.mem_union_left _ h)),
          hU, Matrix.add_apply]
      · rw [dite_eq_left hxB, dite_eq_right hyB,
          corr_apply_eq_zero_of_col A _ (fun u hu => (hsp y hy hyB u hu).2)]
    · rw [dite_eq_right hxB, corr_apply_eq_zero_of_row A _ (fun u hu => (hsp x hx hxB u hu).1)]

omit [LinearOrder V] in
theorem pi_entry_cost (A Fa Fb : Matrix V V K) {a b : ℕ} (f : Fin a → V) (g : Fin b → V) :
    (Counted.pi fun i : Fin a => Counted.pi fun j : Fin b => entry A Fa Fb (f i) (g j)).cost.total =
      2 * (a * b) := by
  simp [Finset.card_univ, OpCount.total]
  ring

/-- The cost of one frontal step with `p = |s|` and `q = |Bd|`: one dense inversion of size `p`,
two products of size `p + q`, and `2 (p + q) ^ 2 + 2` further operations. -/
def frontCost (alg : MatMulAlgorithm K) (p q : ℕ) : ℕ :=
  BlockInverse.costBound alg (Nat.clog 2 p) + 2 * alg.bound (p + q) + 2 * ((p + q) * (p + q)) + 2

/-- **Operation count of the frontal step.** -/
theorem frontStep_cost_le (alg : MatMulAlgorithm K) (A Fa Fb : Matrix V V K) (da db : K)
    (s Bd : Finset V) :
    (frontStep alg A Fa Fb da db s Bd).cost.total ≤ frontCost alg s.card Bd.card := by
  simp only [frontStep, Counted.cost_bind, Counted.cost_pure, OpCount.total_add, Op.cost_mul,
    OpCount.total_mk, OpCount.total_zero, pi_entry_cost, sumUpd_cost]
  have hinv : ∀ M : SqMat s.card K, (FastDet.invDet alg M).cost.total ≤
      BlockInverse.costBound alg (Nat.clog 2 s.card) := fun M => FastDet.invDet_cost_le alg M
  have hr : ∀ {p q r : ℕ} (hp : p ≤ s.card + Bd.card) (hr : r ≤ s.card + Bd.card)
      (X : Matrix (Fin p) (Fin q) K) (Y : Matrix (Fin q) (Fin r) K),
      (rectMul alg (s.card + Bd.card) hp hr X Y).cost.total ≤ alg.bound (s.card + Bd.card) :=
    fun hp hr X Y => rectMul_cost_le alg _ hp hr X Y
  grw [hinv, hr, hr]
  simp only [frontCost]
  ring_nf
  omega
end Front

end Frontal

end

end FastGE
