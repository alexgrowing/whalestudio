import Mathlib
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.LintegralImageEqLintegralNormSqDetMul
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory ReciprocityTheory.AnForm.A

noncomputable section

def HolomorphicFibreSumInt.Statement : Prop :=
  ∀ (d : ℕ) (Ω : Set (Fin d → ℂ)) (τ : (Fin d → ℂ) → Fin d → ℂ) (H : (Fin d → ℂ) → ℝ),
    IsOpen Ω → DifferentiableOn ℂ τ Ω → (∀ y, {t | t ∈ Ω ∧ τ t = y}.Finite) →
    IntegrableOn (fun t => Complex.normSq (jacC τ t).det * H t) Ω →
      Integrable (fun y => ∑ᶠ t ∈ {t | t ∈ Ω ∧ τ t = y}, H t) ∧
        ∫ y, (∑ᶠ t ∈ {t | t ∈ Ω ∧ τ t = y}, H t) =
          ∫ t in Ω, Complex.normSq (jacC τ t).det * H t

end

end GroundTheory.Heights₂.Heights
