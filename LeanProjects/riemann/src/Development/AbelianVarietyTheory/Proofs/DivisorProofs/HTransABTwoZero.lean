import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KFacDifferentiable
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

noncomputable section

namespace GlobalTheory.HeckeTwo

open MeasureTheory

def hTransAB (a b : ℕ) (σ : ℂ) (ν y : ℝ) : ℂ :=
  ∫ t : ℝ, ((t : ℂ) + (y : ℂ) * I)⁻¹ ^ a * ((starRingEnd ℂ) ((t : ℂ) + (y : ℂ) * I))⁻¹ ^ b *
    ((‖(t : ℂ) + (y : ℂ) * I‖ : ℝ) : ℂ) ^ (-2 * σ) * Complex.exp (-(2 * (Real.pi : ℂ) * I * (ν : ℂ) * (t : ℂ)))

theorem hTransAB_two_zero (σ : ℂ) (ν y : ℝ) : hTransAB 2 0 σ ν y = hTrans σ ν y := by
  unfold hTransAB hTrans phi
  congr 1; funext t
  simp only [pow_zero, mul_one]

variable {F : Type} [Field F] [NumberField F]

def termQ (σ : ℂ) (b ν : F) (q : Emb F → ℕ) (z : Emb F → ℂ) : ℂ :=
  ∏ τ : Emb F, (Complex.exp (2 * (Real.pi : ℂ) * I * ((τ ν * τ b * (z τ).re : ℝ) : ℂ)) *
    iteratedDeriv (q τ) (hTrans σ (τ ν)) (τ b * (z τ).im))

theorem termQ_zero (σ : ℂ) (b ν : F) (z : Emb F → ℂ) : termQ σ b ν 0 z = fTerm σ z b ν := by
  unfold termQ fTerm
  simp only [Pi.zero_apply, iteratedDeriv_zero]

end GlobalTheory.HeckeTwo
