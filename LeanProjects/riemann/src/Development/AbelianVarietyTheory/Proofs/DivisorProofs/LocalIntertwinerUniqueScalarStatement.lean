import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalIntertwinerUniqueScalar
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingTrRep
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeilTr MeasureTheory
open scoped Matrix ENNReal

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_intertwiner_unique_scalar : ∀ (F : Type) [Field F] [NumberField F] (v : Pl F) [Invertible (2 : Fv F v)] (κ : Type) [Fintype κ]
    (ψv : AddChar (Fv F v) ℂ), Continuous ψv → ψv ≠ 1 →
    ∀ (T : ((κ → Fv F v) → ℂ) →ₗ[ℂ] (κ → Fv F v) → ℂ) (A : (κ → Fv F v) × (κ → Fv F v) → (κ → Fv F v) × (κ → Fv F v)),
      (∀ φ ∈ SB (κ → Fv F v), T φ ∈ SB (κ → Fv F v)) →
      (∀ w, ∀ φ ∈ SB (κ → Fv F v), T (schr ψv w φ) = schr ψv (A w) (T φ)) →
      ∃ c : ℝ, 0 ≤ c ∧ ∀ μ : @Measure (κ → Fv F v) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
        ∀ φ ∈ SB (κ → Fv F v), ∀ φ' ∈ SB (κ → Fv F v),
          @integral _ ℂ _ _ (borel _) μ (fun x => T φ x * starRingEnd ℂ (T φ' x)) =
            (c : ℂ) * @integral _ ℂ _ _ (borel _) μ (fun x => φ x * starRingEnd ℂ (φ' x)) := by
  first | exact @GlobalTheory.CompactOpenLattice.inner_eq_const_mul | exact GlobalTheory.CompactOpenLattice.inner_eq_const_mul | (intros; apply GlobalTheory.CompactOpenLattice.inner_eq_const_mul <;> assumption)
