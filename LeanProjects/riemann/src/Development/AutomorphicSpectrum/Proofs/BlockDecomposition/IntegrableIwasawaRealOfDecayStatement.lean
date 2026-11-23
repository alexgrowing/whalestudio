import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableIwasawaRealOfDecay
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
theorem _root_.GlobalTheory.T.integrable_iwasawa_real_of_decay : ∀ (F : ℝˣ × ℝˣ × ℝ → ℂ) (C p q N : ℝ), AEStronglyMeasurable F GL2LocalData.mIwR → 0 < p → 0 < q → p < N → q < N → (∀ (a b : ℝˣ) (θ : ℝ), ‖F (a, b, θ)‖ ≤ C * (|(a : ℝ)| ^ p * (1 + |(a : ℝ)|) ^ (-N)) * (|(b : ℝ)| ^ q * (1 + |(b : ℝ)|) ^ (-N))) → Integrable F GL2LocalData.mIwR := by
  first | exact @GlobalTheory.CompanionTheory.GL2Factorization.integrable_mIwR_of_product_bound | exact GlobalTheory.CompanionTheory.GL2Factorization.integrable_mIwR_of_product_bound | (intros; apply GlobalTheory.CompanionTheory.GL2Factorization.integrable_mIwR_of_product_bound <;> assumption)
