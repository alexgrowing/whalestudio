import Mathlib
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.StatementM
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.TopsChoicePartA
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.TopsChoicePartB
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.LogarithmEquivalence
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.TheoremSFromKOneOf

noncomputable section

open scoped BigOperators
open Finset

namespace Formalism.InvariantFactorPaths.G7

open Formalism.DworkPowerSeriesWeights (Integral mvExp jetPair mfact)
open Formalism.FG.IntegralSubstitution (integral_mul integralSubstV)
open TwoS

theorem norm_unif_pow {K : Type} [NormedField K] {p : ℕ} (hp : p.Prime)
    (hn : ‖(p : K)‖ = (p : ℝ)⁻¹) {ϖ : K} (hϖ : ϖ ^ (p ^ 2 - 1) = (p : K)) :
    ‖ϖ ^ (p + 1)‖ = (p : ℝ) ^ (-(1 / ((p : ℝ) - 1))) := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) ≤ (p : ℝ) := by linarith
  have h1 : (p : ℝ) - 1 ≠ 0 := by intro h; linarith
  have h2 : (p : ℝ) + 1 ≠ 0 := by intro h; linarith
  have h3 : (p : ℝ) ^ 2 - 1 ≠ 0 := by
    have : (p : ℝ) ^ 2 - 1 = ((p : ℝ) - 1) * ((p : ℝ) + 1) := by ring
    rw [this]
    exact mul_ne_zero h1 h2
  rw [norm_pow, norm_unif hp hn hϖ, ← Real.rpow_natCast, ← Real.rpow_mul (inv_nonneg.2 hp0),
    Real.inv_rpow hp0, Real.rpow_neg hp0]
  congr 2
  push_cast
  field_simp
  ring

namespace MPl

section Alg

variable {K Pl : Type} [Field K] {ι : Pl → Type}

variable [Fintype Pl]

abbrev eqv : ((Σ v, ι v) →₀ ℕ) ≃+ (∀ v, ι v →₀ ℕ) := Finsupp.sigmaFinsuppAddEquivPiFinsupp

variable [DecidableEq Pl]

end Alg

end MPl

open MPl

end Formalism.InvariantFactorPaths.G7
