import Mathlib
import ReciprocityTheory.AnalyticForms.PotentialTheory.PLLocalStatement
import GroundTheory.HeightsAndTheta.Heights.Intersections.AnalyticResolutionHypothesesProjectiveLine
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

open ReciprocityTheory.AnForm.M

theorem projectiveLineZeroForm_holds.proof : projectiveLineZeroForm_holds.Statement := by
  intro e X _ _ _ A L s W B hL hs hSNC hB v hv Φ hΦ
  have h := poincareLelong A L s ![1] ![W]
    (Fin.cons B (fun i => i.elim0) : ∀ k, FinHolAtlas e ((![W] : Fin 1 → Set X) k))
    hL hs hSNC (Fin.cons hB (fun i => i.elim0)) v hv Φ hΦ
  rw [Fin.sum_univ_one] at h
  have h1 : (((![1] : Fin 1 → ℕ) 0 : ℕ) : ℝ) = 1 := by simp
  rw [h1, one_mul] at h
  exact h

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
