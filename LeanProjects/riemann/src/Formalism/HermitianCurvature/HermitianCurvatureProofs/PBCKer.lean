import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBCStmt
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TheoremPIntegralOfPlaces
import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdmissibleWordMemBoundedLetterLists

namespace Formalism.FourierDecayAlt.P.PBC

open Formalism.FourierDecayAlt Finset Filter Topology MeasureTheory
open scoped ComplexConjugate ComplexOrder

noncomputable section

open Classical

theorem sum_sub_weight {Z J : Type} (P : Finset Z) (Y : J → Finset Z) (hY : ∀ j, Y j ⊆ P) (a : J → Z → ℂ)
    (j : J) (g : Z → ℂ) :
    ∑ p : P, (if (p : Z) ∈ Y j then a j p else 0) * g p = ∑ z ∈ Y j, a j z * g z := by
  simp only [ite_mul, zero_mul]
  rw [Finset.sum_coe_sort P (fun z => if z ∈ Y j then a j z * g z else 0), Finset.sum_ite_mem,
    Finset.inter_eq_right.mpr (hY j)]

theorem psd_wcompress {Z J : Type} [Fintype J] (P : Finset Z) (H : Z → Z → ℂ) (hH : TB.PSDOn P H)
    (Y : J → Finset Z) (a : J → Z → ℂ) (hY : ∀ j, Y j ⊆ P) :
    Matrix.PosSemidef (Matrix.of fun j k : J =>
      ∑ z ∈ Y j, ∑ z' ∈ Y k, star (a j z) * H z z' * a k z') := by
  let B : Matrix P J ℂ := Matrix.of fun x j => if (x : Z) ∈ Y j then a j x else 0
  have h := hH.conjTranspose_mul_mul_same B
  convert h using 1
  ext j k
  have inner : ∀ x : P, ∑ y : P, star (if (x : Z) ∈ Y j then a j x else 0) * H x y *
      (if (y : Z) ∈ Y k then a k y else 0) =
      (if (x : Z) ∈ Y j then star (a j x) else 0) * ∑ z' ∈ Y k, a k z' * H x z' := by
    intro x
    rw [← sum_sub_weight P Y hY a k (fun z' => H x z'), Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    split_ifs <;> simp [mul_comm, mul_left_comm, mul_assoc]
  simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, B, Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]
  simp only [inner]
  rw [sum_sub_weight P Y hY (fun j z => star (a j z)) j (fun z => ∑ z' ∈ Y k, a k z' * H z z')]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun z' _ => ?_
  ring

theorem psd_herm {Z : Type} (P : Finset Z) (K : Z → Z → ℂ) (hK : TB.PSDOn P K) {p q : Z} (hp : p ∈ P)
    (hq : q ∈ P) : K q p = conj (K p q) := by
  have h := hK.1.apply ⟨p, hp⟩ ⟨q, hq⟩
  simp only [Matrix.of_apply] at h
  rw [← h]
  simp

theorem psd_diag {Z : Type} (P : Finset Z) (K : Z → Z → ℂ) (hK : TB.PSDOn P K) {p : Z} (hp : p ∈ P) :
    0 ≤ K p p := by
  have h := hK.diag_nonneg (i := ⟨p, hp⟩)
  simpa [Matrix.of_apply] using h

theorem psd_entry {Z : Type} (P : Finset Z) (K : Z → Z → ℂ) (hK : TB.PSDOn P K) {p q : Z} (hp : p ∈ P)
    (hq : q ∈ P) : ‖K p q‖ ^ 2 ≤ (K p p).re * (K q q).re := by
  let f : Fin 2 → P := ![⟨p, hp⟩, ⟨q, hq⟩]
  have h := (hK.submatrix f).det_nonneg
  rw [Matrix.det_fin_two] at h
  simp only [Matrix.submatrix_apply, Matrix.of_apply, f, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons] at h
  have hqp := psd_herm P K hK hp hq
  rw [hqp, Complex.mul_conj] at h
  have hpd := psd_diag P K hK hp
  have hqd := psd_diag P K hK hq
  have e1 : (K p p) = ((K p p).re : ℂ) := by
    apply Complex.ext <;> simp [(Complex.nonneg_iff.mp hpd).2.symm]
  have e2 : (K q q) = ((K q q).re : ℂ) := by
    apply Complex.ext <;> simp [(Complex.nonneg_iff.mp hqd).2.symm]
  rw [e1, e2, Complex.normSq_eq_norm_sq, ← Complex.ofReal_mul,
    ← Complex.ofReal_sub, Complex.zero_le_real] at h
  linarith

theorem psd_entry_le {Z : Type} (P : Finset Z) (K : Z → Z → ℂ) (hK : TB.PSDOn P K) {p q : Z} (hp : p ∈ P)
    (hq : q ∈ P) (B : ℝ) (hBp : ‖K p p‖ ≤ B) (hBq : ‖K q q‖ ≤ B) : ‖K p q‖ ≤ B := by
  have h := psd_entry P K hK hp hq
  have hp' : (K p p).re ≤ B := (Complex.re_le_norm _).trans hBp
  have hq' : (K q q).re ≤ B := (Complex.re_le_norm _).trans hBq
  have hpd := (Complex.nonneg_iff.mp (psd_diag P K hK hp)).1
  have hqd := (Complex.nonneg_iff.mp (psd_diag P K hK hq)).1
  have hB : 0 ≤ B := (norm_nonneg _).trans hBp
  have h2 : ‖K p q‖ ^ 2 ≤ B ^ 2 := h.trans (by nlinarith)
  nlinarith [norm_nonneg (K p q)]

end

end Formalism.FourierDecayAlt.P.PBC
