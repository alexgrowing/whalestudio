import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.GenericPointSectionHypotheses
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

noncomputable section

universe u w

def InterSumTopVanish.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (n : ℕ) (pp : Ideal (Poly k N)) (L : Fin (n + 1) → LineBundle k x), IsSubvar x pp n →
      ∀ᶠ c : ℕ in atTop, interSum pp (fun i => (L i).toSubSystem) c = 0

end

end GroundTheory.Heights₂.Heights.Kleiman
