import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactSupportPartialFourierIntegral
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.WeilM GlobalTheory.AdelicU Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compact_support_partial_fourier_integral : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (ψ : AddChar (AF F) ℂ),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → ∀ Φ ∈ GlobalTheory.WeilM.schA F κ,
    ∃ K : Set (κ → Af F), IsCompact K ∧
      ∀ μ : @MeasureTheory.Measure (κ → AF F) (borel _), @MeasureTheory.Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∀ w : (κ → AF F) × (κ → AF F),
        @MeasureTheory.integral _ ℂ _ _ (borel _) μ (fun x => Φ x * starRingEnd ℂ (GlobalTheory.WeilM.schr ψ w Φ x)) ≠ 0 →
        (fun i => (w.1 i).2) ∈ K ∧ (fun i => (w.2 i).2) ∈ K := by
  first | exact @GlobalTheory.CoefSupp.coef_supp | exact GlobalTheory.CoefSupp.coef_supp | (intros; apply GlobalTheory.CoefSupp.coef_supp <;> assumption)
