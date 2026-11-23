import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.MahlerMinusConeIntegralIndep
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.IsSigmaCompactConeInter
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.IntegralFubiniStudySumConeStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SphereMeanNormalizedGroupsStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.AePolynomialNonvanishingRowsStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ChowFormFibreSpecializationStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.AeFibrePointsCardEqDegreeStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.GaussianMatrixMeasurePosFiniteStatement
set_option maxSynthPendingDepth 1
open GroundTheory.Heights₂.Heights MeasureTheory MvPolynomial Matrix GlobalTheory.CompanionTheory.Ar.Short.Crofton
open scoped ENNReal

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mahler_minus_cone_integral_indep : ∀ (n e δ : ℕ) (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ))
  (g : MvPolynomial (Fin (e + 1) × Fin n) ℂ) (u u' : Fin n → ℂ),
  IsProjPrime W → IsChowForm W (e + 1) g → IsMultiHomog δ g → linForm u ∉ W → linForm u' ∉ W →
    mahler h e (specFirst g u) - coneIntegral h W e (fsLog h u) =
      mahler h e (specFirst g u') - coneIntegral h W e (fsLog h u') := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Short.Crofton.defect_eq_of_linForm_notMem | exact GlobalTheory.CompanionTheory.Ar.Short.Crofton.defect_eq_of_linForm_notMem | (intros; apply GlobalTheory.CompanionTheory.Ar.Short.Crofton.defect_eq_of_linForm_notMem <;> assumption)
