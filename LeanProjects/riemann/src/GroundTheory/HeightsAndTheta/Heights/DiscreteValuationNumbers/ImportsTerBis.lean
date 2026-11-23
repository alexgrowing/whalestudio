import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.BundleObjects
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.InstFintypeSumElim
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle)

universe u v w

def GradedFrameCharacterisation.Statement : Prop :=
  ∀ (o : Type u) [CommRing o] (Ω : Type v) [Field Ω] [Algebra o Ω] (K : Type) [Fintype K]
    (ι : K → Type) [∀ k, Fintype (ι k)] (y : (Σ k, ι k) → Ω) (N : ℕ) (E : Type w)
    [AddCommGroup E] [Module Ω E] (B : ChartBundle o (segreVec y) N E)
    (w : Module.Basis (Fin N) Ω E) (b : Fin N → K → ℤ),
    IsFlagFrame y B w b ↔ IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsGradedFrame o y B
      (fun i => Submodule.span Ω (w '' {j | (j : ℕ) < i})) b w

end GroundTheory.Heights₂.Heights.NumbersDVR
