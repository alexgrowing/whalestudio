import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsGraphGenTwistBundleZero
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (secOver GeneratesOver)

def BundlePair.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Ω : Type) [Field Ω] [Algebra S Ω] (y : (Σ k, ι k) → Ω) (k₀ : K) (N : ℕ) (e : ι k₀ ≃ Fin (N + 1)),
    IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase S y k₀ → ∀ γ β : K → ℤ,
      ∃ G B : Kleiman.LineBundle S (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm),
        (∀ b : ℕ, (G.twist (B.pow b)).secs = secOver S y (γ + b • β)) ∧
        ∀ (n : ℕ) (η : Fin n → Ω),
          ((∀ j, η j ∈ secOver S y β) ∧ GeneratesOver S y β η) ↔
            ((∀ j, η j ∈ B.secs) ∧
              ∀ I, Submodule.span (Kleiman.chartRing S (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) I) (Set.range η) =
                B.sub I)

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
