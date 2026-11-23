import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SnapperCutObj
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

def MulQuotEq.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (F₁ F₂ G₁ G₂ : SubSystem k x Ω) (s : Ω),
    (∀ I, ∀ y ∈ F₁.sub I, s * y ∈ G₁.sub I) →
    (∀ I, ∀ z ∈ G₁.sub I, ∃ y ∈ F₁.sub I, z - s * y ∈ G₂.sub I) →
    (∀ I, ∀ y ∈ F₁.sub I, (s * y ∈ G₂.sub I ↔ y ∈ F₂.sub I)) →
    eulerCharQuot k G₁ G₂ = eulerCharQuot k F₁ F₂

end

end GroundTheory.Heights₂.Heights.Kleiman
