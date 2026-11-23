import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ClassListMapDomainPerm
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.SameGenericSymm
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NumbersDVR.BundleExamples

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)

def FlagFrameOfFullFlag.Statement : Prop :=
  ∀ (F : Type) [Field F] (Ω : Type) [Field Ω] [Algebra F Ω] (K : Type) [Fintype K]
    (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (e : ℕ),
    ReciprocityTheory.ChartRestriction.G.AI.I1.IsProjVarF (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal F x) e →
    ∀ (N : ℕ) (E : Type) [AddCommGroup E] [Module Ω E]
      (B : ChartBundle F (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mseg x) N E)
      (fl : IndefiniteRowSideFullHecke.NumbersDVR.Bundles.FullFlag F x B),
      ∃ w : Module.Basis (Fin N) Ω E, IsFlagFrame x B w fl.deg

end GroundTheory.Heights₂.Heights.NumbersDVR.BundleExamples
