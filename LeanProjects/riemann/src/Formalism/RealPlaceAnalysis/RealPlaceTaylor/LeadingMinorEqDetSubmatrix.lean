import Formalism.RealPlaceAnalysis.LminorPos

open Matrix
open scoped ComplexOrder

noncomputable section

namespace Formalism.REAL

lemma exp_posDef_of_hermitian {n : ℕ} (Y : Matrix (Fin n) (Fin n) ℂ) (hY : Yᴴ = Y) :
    (NormedSpace.exp Y).PosDef := by
  set B := NormedSpace.exp ((1 / 2 : ℂ) • Y) with hBdef
  have hBh : Bᴴ = B := by
    rw [hBdef, ← Matrix.exp_conjTranspose, conjTranspose_smul, hY]
    congr 2
    simp
  have hsplit : Y = (1 / 2 : ℂ) • Y + (1 / 2 : ℂ) • Y := by
    rw [← add_smul]; norm_num
  have hexp : NormedSpace.exp Y = Bᴴ * B := by
    rw [hBh, hBdef, ← Matrix.exp_add_of_commute _ _ (Commute.refl _), ← hsplit]
  have hu : IsUnit B := Matrix.isUnit_exp _
  rw [hexp]
  exact Matrix.PosDef.conjTranspose_mul_self B (Matrix.mulVec_injective_iff_isUnit.mpr hu)

lemma leading_minor_eq_det_submatrix {n : ℕ} (x : Matrix (Fin n) (Fin n) ℂ) (i : Fin (n + 1)) :
    lminor x i = (x.submatrix (Fin.castLE (Nat.lt_succ_iff.mp i.isLt))
      (Fin.castLE (Nat.lt_succ_iff.mp i.isLt))).det := rfl

theorem leading_minors_positive : LminorPos := by
  intro n Y hY i
  have hP := (exp_posDef_of_hermitian Y hY).submatrix (Fin.castLE_injective (Nat.lt_succ_iff.mp i.isLt))
  have h := hP.det_pos
  rw [← leading_minor_eq_det_submatrix] at h
  obtain ⟨h1, h2⟩ := Complex.pos_iff.mp h
  exact ⟨h2.symm, h1⟩

end Formalism.REAL
