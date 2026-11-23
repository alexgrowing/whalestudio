import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsBisExtra
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver)

def SpanSecs.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (k₀ : K) (N : ℕ) (e : ι k₀ ≃ Fin (N + 1))
    (x : Fin (N + 1) → Ω), x = IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm → IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y k₀ →
      ∀ (T : Set Ω) (d : ℤ) (s : Ω),
        s ∈ (⨅ I : Kleiman.Chart x,
            (Submodule.span (Kleiman.chartRing F x I) T * Kleiman.twistMod F x d I).restrictScalars F) ↔
          ∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) →
            s * y ⟨k₀, c k₀⟩ ^ (-d) ∈ Submodule.span (chartRingOver F y c) T

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
