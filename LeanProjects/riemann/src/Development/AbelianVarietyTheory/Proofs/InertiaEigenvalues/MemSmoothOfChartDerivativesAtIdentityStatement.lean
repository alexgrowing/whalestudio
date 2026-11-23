import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSmoothOfChartDerivativesAtIdentity
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumLieCoord
open NumberField MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.JSW
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_smooth_of_chart_derivatives_at_identity : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (K : Set (GA E a → ℂ)),
    (∀ f ∈ K, ∃ (ι : Type) (_ : Fintype ι) (fs : ι → GA E a → ℂ) (ℓ : ι → (Lie E a →L[ℝ] ℂ)), (∀ i, fs i ∈ K) ∧
      ∀ g, HasFDerivAt (chart f g) (∑ i, fs i g • ℓ i) (oneL E a)) → ∀ f ∈ K, f ∈ Sm E a := by
  first | exact @GlobalTheory.SmOfDeriv.mem_Sm_of_hasFDerivAt | exact GlobalTheory.SmOfDeriv.mem_Sm_of_hasFDerivAt | (intros; apply GlobalTheory.SmOfDeriv.mem_Sm_of_hasFDerivAt <;> assumption)
