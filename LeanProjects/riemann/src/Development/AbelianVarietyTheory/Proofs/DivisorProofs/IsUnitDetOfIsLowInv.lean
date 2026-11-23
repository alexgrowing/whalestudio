import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CellOpenLe

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam

namespace GlobalTheory.ShFam.Cell

section Mat

variable {R : Type} [CommRing R] {m : ℕ}

theorem IsLowInv.blockTriangular {L : Matrix (Fin m) (Fin m) R} (h : IsLowInv L) :
    L.BlockTriangular OrderDual.toDual :=
  fun i j hij => h.1 i j (OrderDual.toDual_lt_toDual.1 hij)

theorem upMat_blockTriangular (a : Above m → R) : (upMat a).BlockTriangular id := fun i j hij => by
  have hij' : j < i := hij
  unfold upMat
  rw [dif_neg (not_lt.2 (le_of_lt hij')), if_neg (ne_of_gt hij')]

@[simp] theorem upMat_diag (a : Above m → R) (i : Fin m) : upMat a i i = 1 := by
  simp [upMat]

theorem IsLowInv.mul {B L : Matrix (Fin m) (Fin m) R} (hB : IsLowInv B) (hL : IsLowInv L) : IsLowInv (B * L) := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    rcases lt_or_ge i k with h | h
    · rw [hB.1 i k h, zero_mul]
    · rw [hL.1 k j (lt_of_le_of_lt h hij), mul_zero]
  · have : (B * L) i i = B i i * L i i := by
      rw [Matrix.mul_apply]
      refine Finset.sum_eq_single i (fun k _ hk => ?_) (by simp)
      rcases lt_or_gt_of_ne hk with h | h
      · rw [hL.1 k i h, mul_zero]
      · rw [hB.1 i k h, zero_mul]
    rw [this]
    exact (hB.2 i).mul (hL.2 i)

theorem InCell.mul_left {B M : Matrix (Fin m) (Fin m) R} {w : Equiv.Perm (Fin m)} {a : Above m → R}
    (hB : IsLowInv B) (h : InCell M w a) : InCell (B * M) w a := by
  obtain ⟨L, hL, e⟩ := h
  refine ⟨B * L, hB.mul hL, ?_⟩
  rw [Matrix.mul_assoc, ← e]
  ext i j
  simp [Matrix.mul_apply]

theorem upMat_map {S : Type} [CommRing S] (f : R →+* S) (a : Above m → R) :
    (upMat a).map f = upMat (f ∘ a) := by
  ext i j
  simp only [Matrix.map_apply, upMat, Function.comp_apply]
  split_ifs <;> simp

theorem IsLowInv.map {S : Type} [CommRing S] (f : R →+* S) {L : Matrix (Fin m) (Fin m) R} (h : IsLowInv L) :
    IsLowInv (L.map f) :=
  ⟨fun i j hij => by simp [h.1 i j hij], fun i => (h.2 i).map f⟩

theorem InCell.map {S : Type} [CommRing S] (f : R →+* S) {M : Matrix (Fin m) (Fin m) R} {w : Equiv.Perm (Fin m)}
    {a : Above m → R} (h : InCell M w a) : InCell (M.map f) w (f ∘ a) := by
  obtain ⟨L, hL, e⟩ := h
  refine ⟨L.map f, hL.map f, ?_⟩
  rw [← upMat_map, ← Matrix.map_mul, ← e]
  rfl

theorem isUnit_det_of_isLowInv {L : Matrix (Fin m) (Fin m) R} (h : IsLowInv L) : IsUnit L.det := by
  rw [Matrix.det_of_lowerTriangular L h.blockTriangular]
  exact ⟨∏ i, (h.2 i).unit, by rw [Units.coe_prod]; simp⟩

theorem det_upMat (a : Above m → R) : (upMat a).det = 1 := by
  rw [Matrix.det_of_upperTriangular (upMat_blockTriangular a)]
  simp

theorem upMat_eq_of_isLowInv {L L' : Matrix (Fin m) (Fin m) R} {a a' : Above m → R} (hL : IsLowInv L)
    (hL' : IsLowInv L') (e : L * upMat a = L' * upMat a') : a = a' := by
  have hd' := isUnit_det_of_isLowInv hL'
  have hdu : IsUnit (upMat a).det := by rw [det_upMat]; exact isUnit_one
  haveI := Matrix.invertibleOfIsUnitDet L' hd'
  haveI := Matrix.invertibleOfIsUnitDet (upMat a) hdu
  set N := L'⁻¹ * L with hN
  have e1 : N * upMat a = upMat a' := by
    rw [hN, Matrix.mul_assoc, e, Matrix.nonsing_inv_mul_cancel_left _ _ hd']
  have hlow : N.BlockTriangular OrderDual.toDual :=
    (Matrix.blockTriangular_inv_of_blockTriangular hL'.blockTriangular).mul hL.blockTriangular
  have e2 : N = upMat a' * (upMat a)⁻¹ := by
    rw [← e1, Matrix.mul_nonsing_inv_cancel_right _ _ hdu]
  have hup : N.BlockTriangular id := by
    rw [e2]
    exact (upMat_blockTriangular a').mul (Matrix.blockTriangular_inv_of_blockTriangular (upMat_blockTriangular a))
  have hoff : ∀ i j, i ≠ j → N i j = 0 := fun i j hij => by
    rcases lt_or_gt_of_ne hij with h | h
    · exact hlow (OrderDual.toDual_lt_toDual.2 h)
    · exact hup h
  have hdiag : ∀ i, N i i = 1 := fun i => by
    have := congrFun (congrFun e1 i) i
    rw [Matrix.mul_apply, Finset.sum_eq_single i (fun k _ hk => by rw [hoff i k (Ne.symm hk), zero_mul])
      (by simp), upMat_diag, upMat_diag, mul_one] at this
    exact this
  have hN1 : N = 1 := by
    ext i j
    by_cases h : i = j
    · subst h; rw [hdiag, Matrix.one_apply_eq]
    · rw [hoff i j h, Matrix.one_apply_ne h]
  rw [hN1, Matrix.one_mul] at e1
  funext p
  have := congrFun (congrFun e1 p.1.1) p.1.2
  simp only [upMat, dif_pos p.2] at this
  exact this

theorem InCell.unique {M : Matrix (Fin m) (Fin m) R} {w : Equiv.Perm (Fin m)} {a a' : Above m → R}
    (h : InCell M w a) (h' : InCell M w a') : a = a' := by
  obtain ⟨L, hL, e⟩ := h
  obtain ⟨L', hL', e'⟩ := h'
  exact upMat_eq_of_isLowInv hL hL' (e.symm.trans e')

end Mat

end GlobalTheory.ShFam.Cell
