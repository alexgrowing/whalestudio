import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SecsTwistSysPtX
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.TwistBundleToSubSystem
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Fintype
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (secOver)

def TensorRealises.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (k₀ : K) (N : ℕ) (e : ι k₀ ≃ Fin (N + 1)),
    IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y k₀ →
    ∀ (L L' : Kleiman.LineBundle F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm)) (β β' : K → ℤ),
      BundleRealises y k₀ L β → BundleRealises y k₀ L' β' → BundleRealises y k₀ (L.tensor L') (β + β')

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
