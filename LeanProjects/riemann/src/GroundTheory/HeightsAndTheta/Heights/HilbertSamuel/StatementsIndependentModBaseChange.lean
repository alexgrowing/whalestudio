import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial

noncomputable section

def IndependentModBaseChange.Statement : Prop :=
  ∀ (σ : Type) (P : Ideal (MvPolynomial σ ℤ)) (r : ℕ) (g : Fin r → MvPolynomial σ ℤ),
    LinearIndependent ℤ (fun i => Ideal.Quotient.mk P (g i)) →
    LinearIndependent ℂ (fun i => Ideal.Quotient.mk (P.map (MvPolynomial.map (Int.castRingHom ℂ)))
      (MvPolynomial.map (Int.castRingHom ℂ) (g i)))

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
