import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimContinuousNormLeOnIccOfDetermined
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemExpSolCons
open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteDim_continuous_norm_le_on_Icc_of_determined : ∀ (V : Submodule ℂ (ℝ → ℂ)), FiniteDimensional ℂ V → (∀ f ∈ V, Continuous f) → ∀ ℓ : ℝ, 0 < ℓ →
    (∀ f ∈ V, (∀ x ∈ Set.Icc 0 ℓ, f x = 0) → f = 0) → ∀ R : ℝ, ∃ C : ℝ, ∀ f ∈ V, ∀ M : ℝ,
      (∀ x ∈ Set.Icc 0 ℓ, ‖f x‖ ≤ M) → ∀ t ∈ Set.Icc (-R) R, ‖f t‖ ≤ C * M := by
  first | exact @GlobalTheory.finiteDim_norm_le_on_Icc_of_determined | exact GlobalTheory.finiteDim_norm_le_on_Icc_of_determined | (intros; apply GlobalTheory.finiteDim_norm_le_on_Icc_of_determined <;> assumption)
