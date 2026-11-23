import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SnapperCutObj
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

def SnapperQuotAdd.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (E : Type v) [AddCommGroup E] [Module Ω E] [Module k E] [IsScalarTower k Ω E]
    (F₁ F₂ F₃ : SubFamily k x E), (∀ I, (F₁.sub I).FG) → (∀ I, F₂.sub I ≤ F₁.sub I) →
    (∀ I, F₃.sub I ≤ F₂.sub I) →
    eulerCharQuot k F₁.toSubSystem F₃.toSubSystem =
      eulerCharQuot k F₁.toSubSystem F₂.toSubSystem + eulerCharQuot k F₂.toSubSystem F₃.toSubSystem

end

end GroundTheory.Heights₂.Heights.Kleiman
