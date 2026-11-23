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

namespace GlobalTheory.CompanionTheory.GL2Factorization.CtIn

theorem continuous_tinvR (m : ℕ) : Continuous (GL2LocalData.tinvR : GL (Fin m) ℝ → GL (Fin m) ℝ) := by
  rw [Units.continuous_iff]
  constructor
  · show Continuous (fun g : GL (Fin m) ℝ => ((g⁻¹ : GL (Fin m) ℝ).val)ᵀ)
    exact (Units.continuous_val.comp continuous_inv).matrix_transpose
  · show Continuous (fun g : GL (Fin m) ℝ => (g.val)ᵀ)
    exact Units.continuous_val.matrix_transpose

theorem tinvR_continuous : ∀ m : ℕ, Continuous (GL2LocalData.tinvR : GL (Fin m) ℝ → GL (Fin m) ℝ) :=
  continuous_tinvR

end GlobalTheory.CompanionTheory.GL2Factorization.CtIn
