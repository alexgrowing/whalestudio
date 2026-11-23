import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.IntegralFubiniStudySumCone
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.IsSigmaCompactConeInter
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.CroftonFormulaFibreSumStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.AeFibrePointsCardEqDegreeStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.GaussianMatrixMeasurePosFiniteStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LogGapMeasurableScaleStableStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FubiniStudyLogLeLogNormStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ConeBallLogGapIntegralStatement
set_option maxSynthPendingDepth 1
open GroundTheory.Heights₂.Heights MeasureTheory MvPolynomial Matrix GlobalTheory.CompanionTheory.Ar.Short.Crofton
open scoped ENNReal

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_fubini_study_sum_cone : ∀ (n e δ : ℕ) (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ))
  (f : MvPolynomial (Fin (e + 1) × Fin n) ℂ) (u : Fin n → ℂ),
  IsProjPrime W → IsChowForm W (e + 1) f → IsMultiHomog δ f → linForm u ∉ W →
    Integrable (fsSum h u (coneSet h W)) (gaussM (e + 1) n) ∧
      ∫ π, fsSum h u (coneSet h W) π ∂(gaussM (e + 1) n) =
        (gaussM (e + 1) n Set.univ).toReal * coneIntegral h W e (fsLog h u) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Short.Crofton.fsSum_crofton | exact GlobalTheory.CompanionTheory.Ar.Short.Crofton.fsSum_crofton | (intros; apply GlobalTheory.CompanionTheory.Ar.Short.Crofton.fsSum_crofton <;> assumption)
