import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GlobSet

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc GlobalTheory.Unfold GlobalTheory.LocOver GlobalTheory.GenMass
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG

namespace GlobalTheory.MinorTri

theorem sum_eq_sum_castLE {E : Type} [AddCommMonoid E] {n l : ℕ} (hl : l ≤ n) (φ : Fin n → E)
    (h : ∀ c : Fin n, l ≤ c.val → φ c = 0) : ∑ c, φ c = ∑ c : Fin l, φ (Fin.castLE hl c) := by
  refine (Fintype.sum_of_injective (Fin.castLE hl) (Fin.castLE_injective hl)
    (fun c : Fin l => φ (Fin.castLE hl c)) φ ?_ (fun _ => rfl)).symm
  intro c hc
  apply h
  by_contra hlt
  exact hc ⟨⟨c.val, by omega⟩, Fin.ext rfl⟩

theorem det_block_uni {E : Type} [CommRing E] {n l : ℕ} (hl : l ≤ n) (A : Matrix (Fin n) (Fin n) E)
    (hA : Uni A) : (A.submatrix (Fin.castLE hl) (Fin.castLE hl)).det = 1 := by
  obtain ⟨h0, h1⟩ := hA
  rw [Matrix.det_of_upperTriangular]
  · simp [Matrix.submatrix_apply, h1]
  · intro i j hij
    simp only [Matrix.submatrix_apply]
    apply h0
    rw [Fin.lt_def, Fin.coe_castLE, Fin.coe_castLE]
    exact hij

theorem block_mul_uni {E : Type} [CommRing E] {n l : ℕ} (hl : l ≤ n) (Z A : Matrix (Fin n) (Fin n) E)
    (hA : Uni A) : (Z * A).submatrix (Fin.castLE hl) (Fin.castLE hl) =
      Z.submatrix (Fin.castLE hl) (Fin.castLE hl) * A.submatrix (Fin.castLE hl) (Fin.castLE hl) := by
  obtain ⟨h0, -⟩ := hA
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  rw [sum_eq_sum_castLE hl _ ?_]
  intro c hc
  rw [h0 c (Fin.castLE hl j) (by rw [Fin.lt_def, Fin.coe_castLE]; exact lt_of_lt_of_le j.isLt hc), mul_zero]

theorem det_block_mul_uni {E : Type} [CommRing E] {n l : ℕ} (hl : l ≤ n) (Z A : Matrix (Fin n) (Fin n) E)
    (hA : Uni A) : ((Z * A).submatrix (Fin.castLE hl) (Fin.castLE hl)).det =
      (Z.submatrix (Fin.castLE hl) (Fin.castLE hl)).det := by
  rw [block_mul_uni hl Z A hA, Matrix.det_mul, det_block_uni hl A hA, mul_one]

theorem det_block_transpose_uni_mul {E : Type} [CommRing E] {n l : ℕ} (hl : l ≤ n)
    (Z A : Matrix (Fin n) (Fin n) E) (hA : Uni A) :
    ((A.transpose * Z).submatrix (Fin.castLE hl) (Fin.castLE hl)).det =
      (Z.submatrix (Fin.castLE hl) (Fin.castLE hl)).det := by
  have e : A.transpose * Z = (Z.transpose * A).transpose := by
    rw [Matrix.transpose_mul, Matrix.transpose_transpose]
  rw [e, ← Matrix.transpose_submatrix, Matrix.det_transpose, det_block_mul_uni hl _ _ hA,
    ← Matrix.transpose_submatrix, Matrix.det_transpose]

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E]
  [TopologicalSpace E] [MeasurableSpace E] {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]

theorem h_sum_left (H : HermSp M V) {ι : Type} (s : Finset ι) (c : ι → E) (v : ι → V) (y : V) :
    H.h (∑ i ∈ s, c i • v i) y = ∑ i ∈ s, c i * H.h (v i) y := by
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    have h0 := H.h_smul_left 0 0 y
    simpa using h0
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, H.h_add_left, H.h_smul_left, ih]

theorem h_sum_right (H : HermSp M V) {ι : Type} (s : Finset ι) (c : ι → E) (v : ι → V) (x : V) :
    H.h x (∑ i ∈ s, c i • v i) = ∑ i ∈ s, M.L.cj (c i) * H.h x (v i) := by
  rw [H.h_herm (∑ i ∈ s, c i • v i) x, h_sum_left H, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, ← H.h_herm (v i) x]

theorem Dl_eq_of_tri (H : HermSp M V) {r : ℕ} (f f' g g' : Fin (r + 1) → V) (hg : Tri E f g)
    (hg' : Tri E f' g') (l : ℕ) : H.Dl g g' l = H.Dl f f' l := by
  obtain ⟨A, hA, hAc⟩ := hg
  obtain ⟨A', hA', hA'c⟩ := hg'
  obtain ⟨hA0, hA1⟩ := hA
  have hB : Uni (A.map M.L.cj) := by
    unfold Uni
    exact ⟨fun a b hab => by simp [Matrix.map_apply, hA0 a b hab], fun a => by simp [Matrix.map_apply, hA1 a]⟩
  have hZ : H.Zhat g g' = (A.map M.L.cj).transpose * H.Zhat f f' * A' := by
    ext a b
    simp only [HermSp.Zhat, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply]
    rw [hAc a, hA'c b, h_sum_left H]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [h_sum_right H, mul_comm]
  unfold HermSp.Dl
  split_ifs with hl
  · rw [hZ, det_block_mul_uni hl _ A' hA', det_block_transpose_uni_mul hl _ _ hB]
  · rfl

end GlobalTheory.MinorTri
