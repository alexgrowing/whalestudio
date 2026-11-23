import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AbsNormInverseDifferentIdealPowEqDiscr
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ImV
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN GlobalTheory.SnMass.SkewVol
open scoped TensorProduct ENNReal nonZeroDivisors Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.absNorm_inverseDifferentIdealPow_eq_discr : ∀ (K : Type) [Field K] [NumberField K] (j : ℕ), (FractionalIdeal.absNorm (dInv K j) : ℝ) = (|(discr K : ℝ)| ^ j)⁻¹ := by
  first | exact @GlobalTheory.SnMass.VolN.absNorm_dInv_eq_abs_discr_pow_inv | exact GlobalTheory.SnMass.VolN.absNorm_dInv_eq_abs_discr_pow_inv | (intros; apply GlobalTheory.SnMass.VolN.absNorm_dInv_eq_abs_discr_pow_inv <;> assumption)
