import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KernelOperatorIntegrableContinuousSmooth
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumLieCoord
open NumberField MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.JSW
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernelOperator_integrable_continuous_smooth : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (X : Type) [MeasurableSpace X] (ν : Measure X)
    (k : X → ℂ) (γ : X → GL (Fin a) (Cinf E)), IsRapidInf ν k γ → ∀ φ : Sm E a, Continuous φ.1 →
    (∃ C : ℝ, ∀ g, ‖φ.1 g‖ ≤ C) →
      (∀ g, Integrable (fun x => k x * φ.1 (g * infGL E a (γ x))) ν) ∧ Continuous (kerOp ν k γ φ.1) := by
  first | exact @GlobalTheory.JSW.kerOp_integrable_continuous | exact GlobalTheory.JSW.kerOp_integrable_continuous | (intros; apply GlobalTheory.JSW.kerOp_integrable_continuous <;> assumption)
