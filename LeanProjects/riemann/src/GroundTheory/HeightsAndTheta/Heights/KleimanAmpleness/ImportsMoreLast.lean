import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.CellMeets
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.MemChartSecOverOfMem
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (secOver chartRingOver)

def ModelCechRefine.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)]
    [∀ k, LinearOrder (ι k)] (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (k₀ : K) (N : ℕ)
    (e : ι k₀ ≃ Fin (N + 1)),
    IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y k₀ → ∀ (γ : K → ℤ)
      (T : Kleiman.SubSystem F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) Ω),
      (∀ J, (T.sub J : Set Ω) = chartSecOver F y k₀ e γ J) →
      ∀ n : ℕ, Nonempty (T.H n ≃ₗ[F] cellH F y γ n)

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
