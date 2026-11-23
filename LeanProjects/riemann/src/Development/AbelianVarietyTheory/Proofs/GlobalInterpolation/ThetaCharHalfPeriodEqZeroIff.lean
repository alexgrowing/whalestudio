import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
import Development.AbelianVarietyTheory.Definitions.Foundations.LatticeIntegralCoordinates
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SignedLogMeans
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.EquidistributedConjugates
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.PeriodLatticeAgreement
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.JacobiThetaHalfCharacteristic
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.ThetaConstantWeber
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaTaylorCoeffAlgebraicAndConjugate
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsVariableChangeEqLatticeCurve
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.DifferentiableAtDerivAtZero
import Formalism.GL3MeanSquares.HookFormulaTorsion.FourFoldOrthogonalSum
open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric GlobalTheory.Glob.IntegralWittCoefficients GlobalTheory.IndefiniteRowSideFullHecke

namespace GlobalTheory.Glob.ThetaParity

open Complex

theorem jacobiTheta₂_add_int (z τ : ℂ) (k : ℤ) :
    jacobiTheta₂ (z + (k : ℂ)) τ = jacobiTheta₂ z τ := by
  induction k using Int.induction_on with
  | zero => simp
  | succ k ih =>
    have : z + ((k + 1 : ℤ) : ℂ) = (z + (k : ℂ)) + 1 := by push_cast; ring
    rw [this, jacobiTheta₂_add_left]; exact_mod_cast ih
  | pred k ih =>
    have : z + ((-(k : ℤ) : ℤ) : ℂ) = (z + ((-(k : ℤ) - 1 : ℤ) : ℂ)) + 1 := by push_cast; ring
    have ih' : jacobiTheta₂ (z + ((-(k : ℤ) : ℤ) : ℂ)) τ = jacobiTheta₂ z τ := by exact_mod_cast ih
    rw [← ih', this, jacobiTheta₂_add_left]

theorem jacobiTheta₂_add_int_mul_eq_zero_iff (z τ : ℂ) (l : ℤ) :
    jacobiTheta₂ (z + (l : ℂ) * τ) τ = 0 ↔ jacobiTheta₂ z τ = 0 := by
  induction l using Int.induction_on with
  | zero => simp
  | succ l ih =>
    have : z + ((l + 1 : ℤ) : ℂ) * τ = (z + (l : ℂ) * τ) + τ := by push_cast; ring
    have ih' : jacobiTheta₂ (z + ((l : ℤ) : ℂ) * τ) τ = 0 ↔ jacobiTheta₂ z τ = 0 := by exact_mod_cast ih
    rw [this, jacobiTheta₂_add_left', mul_eq_zero, or_iff_right (Complex.exp_ne_zero _)]
    exact_mod_cast ih'
  | pred l ih =>
    have : z + ((-(l : ℤ) : ℤ) : ℂ) * τ = (z + ((-(l : ℤ) - 1 : ℤ) : ℂ) * τ) + τ := by push_cast; ring
    have ih' : jacobiTheta₂ (z + ((-(l : ℤ) : ℤ) : ℂ) * τ) τ = 0 ↔ jacobiTheta₂ z τ = 0 := by exact_mod_cast ih
    rw [← ih', this, jacobiTheta₂_add_left', mul_eq_zero, or_iff_right (Complex.exp_ne_zero _)]

theorem jacobiTheta₂_shift_eq_zero_iff (z τ : ℂ) (k l : ℤ) :
    jacobiTheta₂ (z + (k : ℂ) + (l : ℂ) * τ) τ = 0 ↔ jacobiTheta₂ z τ = 0 := by
  rw [jacobiTheta₂_add_int_mul_eq_zero_iff, jacobiTheta₂_add_int]

theorem thetaChar_half_period_eq_zero_iff :
    ∀ τ : UpperHalfPlane, ThetaConstantWeber.JacobiProduct τ → ∀ (m n : ℤ) (a b : Fin 2),
    JacobiThetaHalfCharacteristic.IsEvenChar a b →
    (JacobiThetaHalfCharacteristic.thetaChar a b (((m : ℂ) + (n : ℂ) * (τ : ℂ)) / 2) (τ : ℂ) = 0 ↔
      Odd (m + ((b : ℕ) : ℤ)) ∧ Odd (n + ((a : ℕ) : ℤ))) := by
  intro τ hJ m n a b _
  set t : ℂ := (τ : ℂ)

  have hprod : ThetaConstantWeber.thetaConst 0 0 τ * ThetaConstantWeber.thetaConst 0 1 τ * ThetaConstantWeber.thetaConst 1 0 τ ≠ 0 := by
    rw [hJ]
    exact mul_ne_zero two_ne_zero (pow_ne_zero _ (ModularForm.eta_ne_zero τ.2))
  have h00 : jacobiTheta₂ 0 t ≠ 0 := by
    have := left_ne_zero_of_mul (left_ne_zero_of_mul hprod)
    simpa [ThetaConstantWeber.thetaConst, t] using this
  have h01 : jacobiTheta₂ (1 / 2) t ≠ 0 := by
    have := right_ne_zero_of_mul (left_ne_zero_of_mul hprod)
    simpa [ThetaConstantWeber.thetaConst, t] using this
  have h10 : jacobiTheta₂ (t / 2) t ≠ 0 := by
    have := right_ne_zero_of_mul hprod
    simp only [ThetaConstantWeber.thetaConst, mul_eq_zero, Complex.exp_ne_zero, false_or, ne_eq] at this
    simpa [t] using this
  have h11 : jacobiTheta₂ ((1 + t) / 2) t = 0 := by
    rw [add_comm]; exact GlobalTheory.JacobiDeriv.jacobiTheta₂_half_period t

  set p : ℤ := m + ((b : ℕ) : ℤ)
  set q : ℤ := n + ((a : ℕ) : ℤ)
  have hred : JacobiThetaHalfCharacteristic.thetaChar a b (((m : ℂ) + (n : ℂ) * t) / 2) t = 0 ↔
      jacobiTheta₂ ((((p % 2 : ℤ) : ℂ) + ((q % 2 : ℤ) : ℂ) * t) / 2 + ((p / 2 : ℤ) : ℂ) +
        ((q / 2 : ℤ) : ℂ) * t) t = 0 := by
    unfold JacobiThetaHalfCharacteristic.thetaChar
    rw [mul_eq_zero, or_iff_right (Complex.exp_ne_zero _)]
    have hp := Int.emod_add_mul_ediv p 2
    have hq := Int.emod_add_mul_ediv q 2
    have hp' : ((p % 2 : ℤ) : ℂ) + 2 * ((p / 2 : ℤ) : ℂ) = (m : ℂ) + ((b : ℕ) : ℂ) := by
      exact_mod_cast hp
    have hq' : ((q % 2 : ℤ) : ℂ) + 2 * ((q / 2 : ℤ) : ℂ) = (n : ℂ) + ((a : ℕ) : ℂ) := by
      exact_mod_cast hq
    have : ((m : ℂ) + (n : ℂ) * t) / 2 + (((a : ℕ) : ℂ) * t + ((b : ℕ) : ℂ)) / 2 =
        ((((p % 2 : ℤ) : ℂ) + ((q % 2 : ℤ) : ℂ) * t) / 2 + ((p / 2 : ℤ) : ℂ) +
        ((q / 2 : ℤ) : ℂ) * t) := by
      linear_combination (-(1:ℂ)/2) * hp' + (-(t:ℂ)/2) * hq'
    rw [this]
  rw [hred, jacobiTheta₂_shift_eq_zero_iff, Int.odd_iff, Int.odd_iff]
  rcases Int.emod_two_eq_zero_or_one p with hp | hp <;>
    rcases Int.emod_two_eq_zero_or_one q with hq | hq <;>
    rw [hp, hq] <;> push_cast
  · simpa using h00
  · simpa using h10
  · simpa using h01
  · simpa [add_comm] using h11

end GlobalTheory.Glob.ThetaParity
