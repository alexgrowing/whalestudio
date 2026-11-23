import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.ConvolutionSmoothL2

open MeasureTheory Matrix Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Dec
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.Published

def DiscreteSeriesCoefficientsCuspidal : Prop := GlobalTheory.Dec.CoefCusp

theorem discreteSeriesCoefficientsCuspidal_iff : DiscreteSeriesCoefficientsCuspidal ↔
    ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsSqIntIrr ε σ →
      ∀ u v : H, IsKFin ε σ u → IsKFin ε σ v →
      ∀ W : Submodule ℂ (Fin n → ℂ), IsIsoC ε W →
      ∀ ν : @Measure (UJ ε) (borel (UJ ε)), @IsHaarSub (UJ ε) _ _ (borel (UJ ε)) (NW ε W) ν →
      ∀ x y : UJ ε,
        @Integrable ℂ _ _ (UJ ε) (borel (UJ ε)) (fun m => ⟪v, σ (umat (x * m * y)) u⟫_ℂ) ν ∧
          @integral (UJ ε) ℂ _ _ (borel (UJ ε)) ν (fun m => ⟪v, σ (umat (x * m * y)) u⟫_ℂ) = 0 :=
  Iff.rfl

namespace CoefficientsCuspidal

variable {n : ℕ} {ε : Fin n → Bool}

theorem herm_mulVec (g : UJ ε) (a b : Fin n → ℂ) :
    herm (Jm ε) (umat g *ᵥ a) (umat g *ᵥ b) = herm (Jm ε) a b := by
  have hg : (umat g)ᴴ * Jm ε * umat g = Jm ε := g.2
  unfold herm
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, hg]

def conjH (g : UJ ε) : UJ ε ≃ₜ UJ ε := (Homeomorph.mulLeft g).trans (Homeomorph.mulRight g⁻¹)

end CoefficientsCuspidal

end GlobalTheory.Published
