import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.SevenLogLeLOfPowerBound
import Formalism.SharpRestriction.GlobalSchurBounds.JointsL

noncomputable section

namespace Formalism.MainNotions.flipTwoThree

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory

theorem numsL_of_fam_thr {eps : ℝ} (Fm : FamP eps) (hC : Lnk.CountF Fm)
    (hDl : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, |(Fm.L x i).logDerivativeAtOne| ≤ (Fm.L x i).sc.x ^ (Fm.L x i).sc.eps) :
    ∃ Cn₀ : ℝ, ∀ Cn ≥ Cn₀, ∀ cL ≥ (3 : ℝ), ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x,
      JSL.NumsL (Fm.D x i) (Fm.L x i) Cn cL ∧ JSL.WtsL (Fm.D x i) (Fm.L x i) Cn := by
  obtain ⟨C, x0, -, hx⟩ := hC
  exact nums_wts_of_fam Fm ⟨C, x0, fun x hx' i u => (hx x hx' i u).2.1⟩ hDl

theorem numsL_of_fam {eps : ℝ} (Fm : FamP eps) (hC : Lnk.CountF Fm)
    (hDl : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, |(Fm.L x i).logDerivativeAtOne| ≤ (Fm.L x i).sc.x ^ (Fm.L x i).sc.eps) :
    ∃ Cn cL x0 : ℝ, 0 ≤ cL ∧ ∀ x ≥ x0, ∀ i : Fm.Ix x,
      JSL.NumsL (Fm.D x i) (Fm.L x i) Cn cL ∧ JSL.WtsL (Fm.D x i) (Fm.L x i) Cn := by
  obtain ⟨Cn₀, h⟩ := numsL_of_fam_thr Fm hC hDl
  obtain ⟨x0, hx⟩ := h Cn₀ le_rfl 3 le_rfl
  exact ⟨Cn₀, 3, x0, by norm_num, hx⟩

theorem slopesMF_of_count_fam {eps : ℝ} (Fm : FamP eps) (h5 : ConclusionF5 Fm) (h6 : ConclusionF6 Fm) (hC : Lnk.CountF Fm)
    (hDl : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, |(Fm.L x i).logDerivativeAtOne| ≤ (Fm.L x i).sc.x ^ (Fm.L x i).sc.eps)
    (hCV : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (i : Fm.Ix x) u, Nonempty (ColVal (Fm.D x i) u)) : Lnk.SlopesMF Fm := by
  obtain ⟨Cn, cL, x0, hcL, hx⟩ := numsL_of_fam Fm hC hDl
  obtain ⟨x1, hx1⟩ := hCV
  refine slopesMF_of_count Fm Cn cL hcL h5 h6 ⟨max x0 x1, fun x hx' i => ?_⟩ hC
  have h0 := hx x (le_of_max_le_left hx') i
  exact ⟨h0.1, h0.2, hx1 x (le_of_max_le_right hx') i⟩

end Formalism.MainNotions.flipTwoThree

end
