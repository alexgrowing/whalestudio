import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeylTransposeInvIwasawaReal
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
theorem _root_.GlobalTheory.T.weyl_transposeInv_iwasawa_real : ∀ (a b : ℝˣ) (k : GL (Fin 2) ℝ), k.val * k.valᵀ = 1 → ∃ k' : GL (Fin 2) ℝ, k'.val * k'.valᵀ = 1 ∧ GL2LocalData.w2R * GL2LocalData.tinvR (dg2 (a * b) b * k) = dg2 (a * (a * b)⁻¹) (a * b)⁻¹ * k' := by
  first | exact @GlobalTheory.CompanionTheory.GL2Factorization.IwasawaDual.iwasawa_dual | exact GlobalTheory.CompanionTheory.GL2Factorization.IwasawaDual.iwasawa_dual | (intros; apply GlobalTheory.CompanionTheory.GL2Factorization.IwasawaDual.iwasawa_dual <;> assumption)
