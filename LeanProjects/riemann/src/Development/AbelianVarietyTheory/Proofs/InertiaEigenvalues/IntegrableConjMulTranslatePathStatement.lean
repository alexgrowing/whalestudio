import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegrableConjMulTranslatePath
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
open MeasureTheory GlobalTheory.AutomorphicL2Unitary
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integrable_conj_mul_translate_path' : ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [LocallyCompactSpace G] (Γ : Subgroup G) [DiscreteTopology Γ] (μ : Measure G) [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μ] (c : ℝ → G), Continuous c → ∀ {f' : G → ℂ}, MemL2Quotient Γ μ f' → Continuous f' → ∀ (H : L2 Γ μ) (t : ℝ), Integrable (Function.uncurry fun (s : ℝ) (q : GlobalTheory.AutomorphicL2Unitary.Quot Γ) => starRingEnd ℂ (H q) * f' (sec Γ q * c s)) ((volume.restrict (Set.uIoc 0 t)).prod (quotMeasure Γ μ)) := by
  first | exact @GlobalTheory.integrable_conj_mul_translate_path | exact GlobalTheory.integrable_conj_mul_translate_path | (intros; apply GlobalTheory.integrable_conj_mul_translate_path <;> assumption)
