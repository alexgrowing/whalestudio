import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KFacDifferentiable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffOnHeckeEisensteinFourierTerm
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

noncomputable section
namespace GlobalTheory.HeckeTwo.TermDecay

def qZ (σ : ℂ) (a : ℤ) (b m : ℕ) (y t : ℝ) : ℂ :=
  ((t : ℂ) + (y : ℂ) * I) ^ (-a) * (((t ^ 2 + y ^ 2 : ℝ) : ℂ)) ^ (-σ - (b : ℂ)) * (y : ℂ) ^ m

def intZ (σ : ℂ) (ν : ℝ) (a : ℤ) (b m : ℕ) (y : ℝ) : ℂ :=
  ∫ t : ℝ, qZ σ a b m y t * Complex.exp (-(2 * (Real.pi : ℂ) * I * (ν : ℂ) * (t : ℂ)))

theorem term_eq_qZ (σ : ℂ) (ν : ℝ) (a b m : ℕ) (y t : ℝ) :
    GlobalTheory.HeckeTwo.TermSmooth.term σ ν a b m y t =
      qZ σ (a : ℤ) b m y t * Complex.exp (-(2 * (Real.pi : ℂ) * I * (ν : ℂ) * (t : ℂ))) := by
  unfold GlobalTheory.HeckeTwo.TermSmooth.term qZ
  rw [zpow_neg, zpow_natCast, inv_pow]

theorem intT_eq_intZ (σ : ℂ) (ν : ℝ) (a b m : ℕ) (y : ℝ) :
    GlobalTheory.HeckeTwo.TermSmooth.intT σ ν a b m y = intZ σ ν (a : ℤ) b m y := by
  unfold GlobalTheory.HeckeTwo.TermSmooth.intT intZ
  simp_rw [term_eq_qZ]

theorem intZ_eq_fourier (σ : ℂ) (ν : ℝ) (a : ℤ) (b m : ℕ) (y : ℝ) :
    intZ σ ν a b m y = FourierTransform.fourier (qZ σ a b m y) ν := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  unfold intZ
  congr 1
  funext t
  rw [smul_eq_mul, mul_comm]
  congr 1
  push_cast
  ring_nf

end GlobalTheory.HeckeTwo.TermDecay
