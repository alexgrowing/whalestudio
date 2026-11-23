import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormRealWhittakerTorusLe
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
theorem _root_.GlobalTheory.T.norm_real_whittaker_torus_le : ∀ (n : ℤ) (a b : ℝˣ) (k : GL (Fin 2) ℝ), k.val * k.valᵀ = 1 → ‖GL2LocalData.WthR n (dg2 (a * b) b * k)‖ ≤ |(a : ℝ)| ^ (((n.natAbs + 1 : ℕ) : ℝ) / 2) * Real.exp (-(2 * Real.pi * |(a : ℝ)|)) := by
  first | exact @GlobalTheory.CompanionTheory.GL2Factorization.NormWth.norm_WthR_iwasawa_le | exact GlobalTheory.CompanionTheory.GL2Factorization.NormWth.norm_WthR_iwasawa_le | (intros; apply GlobalTheory.CompanionTheory.GL2Factorization.NormWth.norm_WthR_iwasawa_le <;> assumption)
