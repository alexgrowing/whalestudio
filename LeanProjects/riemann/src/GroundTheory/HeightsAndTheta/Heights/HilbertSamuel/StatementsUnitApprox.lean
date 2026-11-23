import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open NumberField

def UnitApprox.Statement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (u : (F →+* ℂ) → ℝ),
    (∀ sg, u (ComplexEmbedding.conjugate sg) = u sg) → ∑ sg, u sg = 0 →
    ∃ C : ℝ, ∀ n : ℕ, ∃ ε : (𝓞 F)ˣ, ∀ sg : F →+* ℂ,
      |Real.log ‖sg ((ε : 𝓞 F) : F)‖ - n * u sg| ≤ C

end GroundTheory.Heights₂.Heights.HilbertSamuel
