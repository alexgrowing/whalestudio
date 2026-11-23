import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.MemChartSecOverOfMem
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (secOver GeneratesOver)

def ChartSecGen.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Ω : Type) [Field Ω] [Algebra S Ω] (y : (Σ k, ι k) → Ω) (k₀ : K) (N : ℕ) (e : ι k₀ ≃ Fin (N + 1)),
    IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase S y k₀ → ∀ (β : K → ℤ) (n : ℕ) (η : Fin n → Ω),
      (∀ j, η j ∈ secOver S y β) →
      (GeneratesOver S y β η ↔
        ∀ I : Kleiman.Chart (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm),
          (Submodule.span (Kleiman.chartRing S (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) I) (Set.range η) : Set Ω) =
            chartSecOver S y k₀ e β I)

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
