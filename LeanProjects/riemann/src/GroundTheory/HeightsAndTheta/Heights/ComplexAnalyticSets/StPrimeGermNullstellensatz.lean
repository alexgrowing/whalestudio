import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StZariskiAnalyticNormality
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.AnalyticGerm
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

noncomputable def holGermIdeal {σ : Type} [Fintype σ] (w : σ → ℂ) {k : ℕ} (f : Fin k → (σ → ℂ) → ℂ) : Ideal (holGerms w) :=
  Ideal.span {φ | ∃ i, (φ : Germ (𝓝 w) ℂ) = (f i : Germ (𝓝 w) ℂ)}

def PrimeGermNullstellensatz.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (w : σ → ℂ) (k : ℕ) (p : Fin k → (σ → ℂ) → ℂ) (g : (σ → ℂ) → ℂ),
    (∀ i, AnalyticAt ℂ (p i) w) → AnalyticAt ℂ g w → (holGermIdeal w p).IsPrime →
    (∀ᶠ z in 𝓝 w, (∀ i, p i z = 0) → g z = 0) →
    ∃ h : Fin k → (σ → ℂ) → ℂ, (∀ i, AnalyticAt ℂ (h i) w) ∧ ∀ᶠ z in 𝓝 w, g z = ∑ i, h i z * p i z

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
