import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

def FibreCompDimZ.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (P : Ideal (MvPolynomial σ ℤ)), P.IsPrime →
    P.comap (C : ℤ →+* MvPolynomial σ ℤ) = ⊥ → ∀ (d p : ℕ), p.Prime →
      ringKrullDim (MvPolynomial σ ℤ ⧸ P) = ((d + 1 : ℕ) : WithBot ℕ∞) →
        ∀ W ∈ (P ⊔ Ideal.span {(C (p : ℤ) : MvPolynomial σ ℤ)}).minimalPrimes,
          ringKrullDim (MvPolynomial σ ℤ ⧸ W) = ((d : ℕ) : WithBot ℕ∞)

end GroundTheory.Heights₂.Heights
