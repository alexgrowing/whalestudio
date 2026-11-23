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

namespace GlobalTheory.CompanionTheory.GL2Factorization

theorem integrable_mIwR_of_product_bound :
    ∀ (F : ℝˣ × ℝˣ × ℝ → ℂ) (C p q N : ℝ), AEStronglyMeasurable F GL2LocalData.mIwR → 0 < p → 0 < q → p < N → q < N → (∀ (a b : ℝˣ) (θ : ℝ), ‖F (a, b, θ)‖ ≤ C * (|(a : ℝ)| ^ p * (1 + |(a : ℝ)|) ^ (-N)) * (|(b : ℝ)| ^ q * (1 + |(b : ℝ)|) ^ (-N))) → Integrable F GL2LocalData.mIwR := by
  intro F C p q N hF hp hq hpN hqN hb
  have h1 := GlobalTheory.CompanionTheory.RealTateConv.integrable_mulR_abs_rpow_mul_one_add_rpow_neg p N hp hpN
  have h2 := GlobalTheory.CompanionTheory.RealTateConv.integrable_mulR_abs_rpow_mul_one_add_rpow_neg q N hq hqN
  have h3 : Integrable (fun _ : ℝ => (1 : ℝ)) (volume.restrict (Set.Ioc 0 (2 * Real.pi))) :=
    integrable_const _
  have h4 := h2.mul_prod h3
  have h5 := h1.mul_prod h4
  have h6 := h5.const_mul C
  refine Integrable.mono' (g := _) h6 hF ?_
  refine Filter.Eventually.of_forall ?_
  rintro ⟨a, b, θ⟩
  refine (hb a b θ).trans (le_of_eq ?_)
  simp only [mul_one]
  ring

end GlobalTheory.CompanionTheory.GL2Factorization
