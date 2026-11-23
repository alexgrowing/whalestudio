import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormZetaIntegrandDecayBound
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.CasselmanShalikaStandardVector
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BndIUnits
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrablePowerWeightUnits
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ValMeasurableEmbedding
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open Ad3.R (G2 Jd md KA lc)
open scoped NumberField.AdeleRing ValuativeRel
open GlobalTheory.CompanionTheory.GL2Factorization
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_zeta_integrand_decay_bound : ∀ (x₃ x₂ s : ℂ) (A B C m : ℝ) (T N : ℕ), 0 < A → 0 < B → ‖x₃‖ ≤ C / (A * B) ^ T / ((1 + A) * (1 + B)) ^ N → ‖x₂‖ ≤ A ^ m → ‖x₃ * x₂ * ((A : ℂ) ^ (s - 3 / 2)) * ((B : ℂ) ^ (2 * s - 1))‖ ≤ C * (A ^ (s.re - 3 / 2 + m - T) * (1 + A) ^ (-(N : ℝ))) * (B ^ (2 * s.re - 1 - T) * (1 + B) ^ (-(N : ℝ))) := by
  first | exact @GlobalTheory.CompanionTheory.GL2Factorization.real_integrand_norm_le_ptw | exact GlobalTheory.CompanionTheory.GL2Factorization.real_integrand_norm_le_ptw | (intros; apply GlobalTheory.CompanionTheory.GL2Factorization.real_integrand_norm_le_ptw <;> assumption)
