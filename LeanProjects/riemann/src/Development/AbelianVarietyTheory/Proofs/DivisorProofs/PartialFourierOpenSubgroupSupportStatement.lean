import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialFourierOpenSubgroupSupport
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.WeilM GlobalTheory.AdelicU Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.partial_fourier_open_subgroup_support : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (ψ : AddChar (AF F) ℂ),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → ∀ Φ ∈ GlobalTheory.WeilM.schA F κ,
    ∃ Mo : AddSubgroup (κ → Af F), IsOpen (Mo : Set (κ → Af F)) ∧
      ∀ μ : @MeasureTheory.Measure (κ → AF F) (borel _), @MeasureTheory.Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∀ w l : (κ → AF F) × (κ → AF F), (∀ i, (l.1 i).1 = 0 ∧ (l.2 i).1 = 0) →
        (fun i => (l.1 i).2) ∈ Mo → (fun i => (l.2 i).2) ∈ Mo →
        @MeasureTheory.integral _ ℂ _ _ (borel _) μ (fun x => Φ x * starRingEnd ℂ (GlobalTheory.WeilM.schr ψ (w + l) Φ x)) =
          @MeasureTheory.integral _ ℂ _ _ (borel _) μ (fun x => Φ x * starRingEnd ℂ (GlobalTheory.WeilM.schr ψ w Φ x)) := by
  first | exact @GlobalTheory.CoefFinPer.coef_transl_fin | exact GlobalTheory.CoefFinPer.coef_transl_fin | (intros; apply GlobalTheory.CoefFinPer.coef_transl_fin <;> assumption)
