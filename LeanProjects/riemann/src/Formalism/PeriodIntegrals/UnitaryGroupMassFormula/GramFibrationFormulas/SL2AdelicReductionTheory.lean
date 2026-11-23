import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GramFibrationFormulas.IsGoodV

open scoped TensorProduct ENNReal
open MeasureTheory NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

noncomputable section

namespace PI.GramFibrationFormulas

def rationalSL2 (F : Type) [Field F] [NumberField F] : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (AF F)) :=
  (Matrix.SpecialLinearGroup.map (algebraMap F (AF F))).range

def SL2AdelicReductionTheory : Prop :=
  ∀ (F : Type) [Field F] [NumberField F],
    (∃ (ω : Set (AF F)) (C : Set (Matrix.SpecialLinearGroup (Fin 2) (AF F))) (t₀ : ℝ),
      IsCompact ω ∧ IsCompact C ∧ 0 < t₀ ∧
      ∀ g : Matrix.SpecialLinearGroup (Fin 2) (AF F), ∃ γ ∈ rationalSL2 F, ∃ y ∈ ω, ∃ T : ℝ, t₀ ≤ T ∧
        ∃ a a' : Ainf F, (∀ w, a w * a' w = 1 ∧ ‖a w‖ = T) ∧ ∃ c ∈ C,
          ((γ * g : Matrix.SpecialLinearGroup (Fin 2) (AF F)) : Matrix (Fin 2) (Fin 2) (AF F)) =
            !![1, y; 0, 1] * !![pairA F a 1, 0; 0, pairA F a' 1] * (c : Matrix (Fin 2) (Fin 2) (AF F))) ∧
    letI : MeasurableSpace (Matrix.SpecialLinearGroup (Fin 2) (AF F)) := borel _
    ∃ μ : Measure (Matrix.SpecialLinearGroup (Fin 2) (AF F)), μ.IsHaarMeasure ∧
      ∃ 𝓕, IsFundamentalDomain (rationalSL2 F) 𝓕 μ ∧ μ 𝓕 < ⊤

end PI.GramFibrationFormulas
