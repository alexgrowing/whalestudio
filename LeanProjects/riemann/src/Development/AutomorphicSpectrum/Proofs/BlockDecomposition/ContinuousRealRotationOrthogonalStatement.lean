import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousRealRotationOrthogonal
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
theorem _root_.GlobalTheory.T.continuous_real_rotation_orthogonal : ∀ ε : Bool, Continuous (fun θ : ℝ => GL2LocalData.kR θ ε) ∧ ∀ θ : ℝ, (GL2LocalData.kR θ ε).val * (GL2LocalData.kR θ ε).valᵀ = 1 := by
  first | exact @GlobalTheory.CompanionTheory.GL2Factorization.OrthParam.kR_continuous_orthogonal | exact GlobalTheory.CompanionTheory.GL2Factorization.OrthParam.kR_continuous_orthogonal | (intros; apply GlobalTheory.CompanionTheory.GL2Factorization.OrthParam.kR_continuous_orthogonal <;> assumption)
