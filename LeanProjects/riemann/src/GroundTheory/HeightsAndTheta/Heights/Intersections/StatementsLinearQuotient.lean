import Mathlib
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial

def LinearQuotient.Statement : Prop :=
  ∀ (F : Type) [Field F] (σ : Type) [Fintype σ] (S : Set (MvPolynomial σ F)),
    (∀ f ∈ S, f.IsHomogeneous 1) →
    ∃ (r : ℕ) (φ : MvPolynomial σ F →ₐ[F] MvPolynomial (Fin r) F), Function.Surjective φ ∧
      RingHom.ker φ = Ideal.span S ∧ ∀ s, (φ (X s)).IsHomogeneous 1

end GroundTheory.Heights₂.Heights.Inter
