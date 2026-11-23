import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ChartRingOverOneBlockBase
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (secOver)

def PullSecsModel.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K₁ : Type) [Fintype K₁] (ι₁ : K₁ → Type) [∀ k, Fintype (ι₁ k)]
    (K₀ : Type) [Fintype K₀] [DecidableEq K₀] (ι₀ : K₀ → Type) [∀ k, Fintype (ι₀ k)]
    (Ω : Type) [Field Ω] [Algebra S Ω] (y₁ : (Σ k, ι₁ k) → Ω) (y₀ : (Σ k, ι₀ k) → Ω) (k₀ : K₀)
    (N N' : ℕ) (e : ι₀ k₀ ≃ Fin (N + 1)) (x : Fin (N + 1) → Ω) (x' : Fin (N' + 1) → Ω),
    x = IndefiniteRowSideFullHecke.Kleiman2.blockVec y₀ k₀ ∘ e.symm → IsNoetherianRing S → (∀ k, ∃ i, y₁ ⟨k, i⟩ ≠ 0) → IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase S y₀ k₀ →
    IndefiniteRowSideFullHecke.Kleiman2.Dominates S y₁ y₀ → IndefiniteRowSideFullHecke.Kleiman2.SameModel S y₁ (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x') →
    ∀ (Q : Kleiman.LineBundle S x) (β : K₀ → ℤ),
      (∀ c : ℤ, (Q.twist (Kleiman.twistSys S x c)).secs =
        secOver S y₀ (β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀)) →
      Kleiman.pullSecs x' Q.toSubSystem = secOver S (IndefiniteRowSideFullHecke.Kleiman2.joinVec y₁ y₀) (IndefiniteRowSideFullHecke.Kleiman2.pullDeg β)

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
