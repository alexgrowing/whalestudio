import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormRapidKernelSmoothSpanSmoothCuspidalBound
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf
import Development.AbelianVarietyTheory.Definitions.Divisors.MemL2OfSmoothVector
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
open NumberField Matrix GlobalTheory.CuspRep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspFormRapidKernelSmoothSpan_smooth_cuspidal_bounded : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), GlobalTheory.Published.CuspFormsBoundedGL → ∀ (π : CuspSub E a), π.IsUnitary → ∀ F ∈ GlobalTheory.JSW.mspanR π, ∃ φ : Sm E a, φ.1 = F ∧ (∀ l : List (Lie E a), (GlobalTheory.GLFin.word l φ).1 ∈ GlobalTheory.JSW.mspanR π) ∧ IsCuspidal F ∧ ∃ C : ℝ, ∀ g, ‖F g‖ ≤ C := by
  first | exact @GlobalTheory.JSW.mspanR_smooth | exact GlobalTheory.JSW.mspanR_smooth | (intros; apply GlobalTheory.JSW.mspanR_smooth <;> assumption)
