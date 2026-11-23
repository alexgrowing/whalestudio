import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Weyl3TransposeInvEmbeddingIwasawa
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
theorem _root_.GlobalTheory.T.weyl3_transposeInv_embedding_iwasawa : ∀ (a b : ℝˣ) (k : GL (Fin 2) ℝ), k.val * k.valᵀ = 1 → ∃ o ∈ O3, GL2LocalData.w3R * GL2LocalData.tinvR (GL2LocalData.emR (dg2 (a * b) b * k)) = dg (a * b)⁻¹ (a * b)⁻¹ (a * b)⁻¹ * (dg (b * a) a 1 * o) := by
  first | exact @GlobalTheory.CompanionTheory.GL2Factorization.DualIw.dual_coords | exact GlobalTheory.CompanionTheory.GL2Factorization.DualIw.dual_coords | (intros; apply GlobalTheory.CompanionTheory.GL2Factorization.DualIw.dual_coords <;> assumption)
