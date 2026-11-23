import Mathlib
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CuspFormBoundedBySupNormAtGoodEmbeddingAllEmbeddStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsMetricDataCmPointComplexEmbeddingStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.FramePolynomialEquivariantAndNeZeroStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MetricChangeOfFrameStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniqueFrameChangeByMatrices
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFramedPointBaseChangeAlgebraMap
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsFieldsSeparately
import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.ExistsPrincipalLattice
import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
import Formalism.LocalToGlobal.ProjectiveLattices.L2DefiniteCuspForms
import Formalism.LocalToGlobal.ProjectiveLattices.NonnegIffOfLiesTotal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NonemptyUnitAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.NonvanishingNearMaximum
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IsotropicCoefficientSplitting
import Formalism.LocalToGlobal.CMDeterminantIdeals.LambdaLowerBound
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

namespace GlobalTheory.LamT

set_option maxHeartbeats 1000000 in

theorem step5Arch_cm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] [DecidableEq (E →+* ℂ)] (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (ξ : ℝ), (∀ σ, GoodEmb c σ → IsUnf (U σ)) → (∀ σ, GoodEmb c σ → ∀ k (τ : E →+* ℂ), ‖τ ((U σ).X k).ξ0‖ = ξ) → 1 ≤ Dw.p + Dw.q → ∀ (z : CMPt Xo c) (f : ℕ) (La : ℝ), z.Good f La → ∀ a n, Dom a n → ∀ F ∈ cusp Xo c U a n, ∀ G : MvPolynomial (FrVar Dw.mult) z.K, IsFrPoly F z.y G → ∀ σ : z.K →+* ℂ, Step5Arch z.e z.Tl.dual z.LamL z.ℓ z.U G (fun b i => a (b, i)) n La (supC Xo c U ξ (goodOf c (σ.comp (algebraMap c.F z.K))) a n F) σ := by
  intro E _ _ _ H Dw l Xo c _ _ r U ξ hU hξ hpq z f La hz a n hD F hF G hG σ
  obtain ⟨yσ, hy⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c z.K
    (CAt (σ.comp (algebraMap c.F z.K))) (embAlg σ) z.y
  obtain ⟨Hm, hpd, hLam, hU', hmet⟩ := GlobalTheory.T.exists_metricData_cmPoint_complexEmbedding E H Dw l Xo c z f La hz σ yσ hy
  have hsec : F ∈ sec Xo c a n := Formalism.L2.Pj.cusp_le_sec Xo c U a n hF
  refine ⟨Hm, hpd, hLam, hU', (GlobalTheory.T.framePolynomial_equivariant_and_ne_zero E H Dw l Xo c z.K z.y a n F hsec G hG).1 σ, ?_⟩
  intro Y hY
  have hdet : ∀ b, IsUnit (Y b).det := by
    intro b
    have h := congrArg Matrix.det (hY b)
    rw [Matrix.det_mul, Matrix.det_one] at h
    exact IsUnit.of_mul_eq_one_right _ h
  obtain ⟨y', hy', -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c (CAt (σ.comp (algebraMap c.F z.K))) yσ
    (fun b => (Y b).transpose) 1 (fun b => by
      have := hdet b
      rwa [← Matrix.det_transpose] at this)
  have hm' := GlobalTheory.T.metric_change_of_frame E H Dw l Xo c _ yσ y' _ _ Y 1 one_ne_zero hy' hmet
  have e1 : (fun b => (Y b).conjTranspose * gramBlock z.e z.U Hm σ b * Y b) = fun _ => 1 := funext hY
  rw [e1, norm_one, one_pow, _root_.one_mul] at hm'
  have hb := GlobalTheory.T.cuspForm_bounded_by_supNorm_at_good_embedding_all_embeddings E H Dw l Xo c r U ξ hU hξ hpq a n hD F hF _ y' _ hm'
  have hev := hG _ (embAlg σ) yσ y' Y hdet hy hy'
  have hT : 0 < z.Tl.n σ := by
    obtain ⟨⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hT, -⟩, -⟩ := hz
    exact hT.2 σ
  rw [Real.sqrt_sq hT.le, hev] at hb
  have hb' : ‖evalFr (MvPolynomial.map σ G) Y‖ ≤
      z.Tl.n σ ^ n * supC Xo c U ξ (goodOf c (σ.comp (algebraMap c.F z.K))) a n F := hb
  have hd : z.Tl.dual.n σ = (z.Tl.n σ)⁻¹ := rfl
  rw [hd, inv_pow, ← div_eq_mul_inv, div_le_iff₀ (pow_pos hT n), _root_.mul_comm]
  exact hb'

end GlobalTheory.LamT
