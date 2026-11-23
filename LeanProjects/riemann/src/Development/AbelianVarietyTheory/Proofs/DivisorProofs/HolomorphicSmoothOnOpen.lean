import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
import ReciprocityTheory.AnalyticForms.AnalyticCharts.Osgood
open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe
open scoped Real ContDiff

namespace GlobalTheory

theorem contDiffOn_real_of_differentiableOn_pt {g : ℕ} {E : Type} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [FiniteDimensional ℂ E] {s : Set (Pt E g)} {φ : Pt E g → ℂ}
    (hs : IsOpen s) (hφ : DifferentiableOn ℂ φ s) : ContDiffOn ℝ ∞ φ s := by
  let e : Pt E g ≃L[ℂ] (Fin (Module.finrank ℂ (Pt E g)) → ℂ) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp)
  have ha : AnalyticOnNhd ℂ φ s := by
    intro z hz
    have h := ReciprocityTheory.AnForm.Osgood.osgood _ (e.symm ⁻¹' s) (φ ∘ e.symm)
      (hs.preimage e.symm.continuous)
      (hφ.comp e.symm.differentiableOn (fun _ h => h)) (e z) (by simpa using hz)
    have h2 := h.comp (e.analyticAt z)
    refine h2.congr (Filter.Eventually.of_forall fun x => ?_)
    simp
  have hc : ContDiffOn ℂ ∞ φ s := (ha.contDiffOn hs.uniqueDiffOn).of_le le_top
  exact hc.restrict_scalars ℝ

end GlobalTheory
