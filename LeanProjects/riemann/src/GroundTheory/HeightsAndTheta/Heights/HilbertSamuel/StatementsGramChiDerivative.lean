import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBergman
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MeasureTheory Set ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.CP

noncomputable section

def GramChiDerivative.Statement : Prop :=
  ∀ {D : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] [MeasurableSpace X]
    [BorelSpace X] (A : FinHolAtlas D X) (L : HolLineBundle A) (W₀ W₁ : Weight L)
    (dV : SmoothVolume A) (n : ℕ) (V : Submodule ℂ (Fin A.n → X → ℂ)) [FiniteDimensional ℂ V],
    V ≤ L.sections n → ∀ (e : Module.Basis (Fin (Module.finrank ℂ V)) ℂ V) (t : ℝ),
      HasDerivAt (fun s : ℝ ↦ chiGram (W₀.lerp W₁ s) dV n (fun a ↦ (e a : Fin A.n → X → ℂ)))
        ((n : ℝ) / 2 * ∫ x, Weight.diff W₁ W₀ x * bergman (W₀.lerp W₁ t) dV V n x ∂dV.μ) t

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
