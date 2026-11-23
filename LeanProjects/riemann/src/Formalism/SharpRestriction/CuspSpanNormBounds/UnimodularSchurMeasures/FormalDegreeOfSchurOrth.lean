import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.FfgZeroOfInt

noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory Matrix Finset
open scoped InnerProductSpace ComplexOrder
open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData Formalism.MainNotions.BridgeLemma

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def FConvEig (χ : ∀ n : ℕ, (Fin n → ℝ) → ℕ → ℂ) : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (E : H →L[ℂ] H), Formalism.QuantumDeterminants.IsHCParam lam → IsDS ε lam σ →
    IsOrthProjOnto E (lowKSub ε lam σ) →
    ∀ Ψ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H), ff_Sph ε σ Ψ → ff_Compr ε E Ψ → ff_Eig ε (χ n lam) Ψ → ff_DSSum ε Ψ →
    ∀ (H' : Type) [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
      (π' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')), ffg_IsSq ε π' → ∀ (x y : H) (a b : H'),
      ∃ F : Matrix (Fin n) (Fin n) ℂ → ℂ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F ∧
        (∀ g₀ : Formalism.REAL.UJ ε, F (umat g₀) =
          ∫ g, ⟪x, Ψ (umat (g * g₀)) y⟫_ℂ * star (coefOn π' a b g) ∂(Formalism.REAL.muG ε)) ∧
        ∀ (k : ℕ), ∀ g ∈ UJset ε, gelfandOp ε k F g = χ n lam k * F g

section Congr

variable {n : ℕ} {ε : Fin n → Bool}

end Congr

end Formalism.MainNotions.LeviCoordinates

end
