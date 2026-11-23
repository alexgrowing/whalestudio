import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.ExistsPrincipalLattice
import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
import Formalism.LocalToGlobal.ProjectiveLattices.L2DefiniteCuspForms
import Formalism.LocalToGlobal.ProjectiveLattices.NonnegIffOfLiesTotal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NonemptyUnitAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.NonvanishingNearMaximum
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IsotropicCoefficientSplitting
import Formalism.LocalToGlobal.CMDeterminantIdeals.LambdaLowerBound
import Formalism.LocalToGlobal.ProjectiveLattices.RosatiLatticeNorms.LinkFD
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.SupAtUnit
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.PointwiseNormSectionEqFlagDomainNorm
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LowerTriIsUnitDet
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedModuliAlgebraicLawsChartWeightIntegrality
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsFieldsSeparately
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MetricDataUniqueStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MetricChangeOfFrameStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.UnifMetricScalarStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsOrthonormalFrameBorelChangeComplexFramedPoStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

namespace GlobalTheory.LamT.OrthoBound

theorem norm_diag_of_triangular {m : ℕ} (Y : Matrix (Fin m) (Fin m) ℂ) (κ : ℝ) (hκ : 0 < κ)
    (hY : ∀ i j, j < i → Y i j = 0) (h : Y.conjTranspose * ((κ : ℂ) • (1 : Matrix (Fin m) (Fin m) ℂ)) * Y = 1)
    (i : Fin m) : ‖Y i i‖ = (Real.sqrt κ)⁻¹ := by
  have h1 : Y.conjTranspose * ((κ : ℂ) • Y) = 1 := by
    rw [← h]; simp
  have hM : ((κ : ℂ) • Y).BlockTriangular id := by
    intro a b hab
    simp [hY a b hab]
  letI : Invertible ((κ : ℂ) • Y) := invertibleOfLeftInverse _ _ h1
  have hinv := Matrix.blockTriangular_inv_of_blockTriangular hM
  rw [Matrix.inv_eq_left_inv h1] at hinv
  have h2 := congrFun (congrFun h1 i) i
  rw [Matrix.mul_apply, Finset.sum_eq_single i, Matrix.one_apply_eq] at h2
  · have h3 : κ * ‖Y i i‖ ^ 2 = 1 := by
      have h4 := congrArg (fun z : ℂ => ‖z‖) h2
      simp only [Matrix.conjTranspose_apply, Matrix.smul_apply, smul_eq_mul, norm_mul, norm_star, norm_one,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos hκ] at h4
      linear_combination h4
    rw [← Real.sqrt_inv]
    symm
    rw [Real.sqrt_eq_iff_mul_self_eq (inv_nonneg.2 hκ.le) (norm_nonneg _)]
    field_simp
    linear_combination -h3
  · intro j _ hj
    rcases lt_or_gt_of_ne hj with hlt | hgt
    · rw [hinv (show id j < id i from hlt), zero_mul]
    · simp [hY j i hgt]
  · simp

theorem cabs_evR_le_supC : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (ξ : ℝ), (∀ σ, GoodEmb c σ → IsUnf (U σ)) → (∀ σ, GoodEmb c σ → ∀ k (τ : E →+* ℂ), ‖τ ((U σ).X k).ξ0‖ = ξ) → 1 ≤ Dw.p + Dw.q → ∀ a n, Dom a n → ∀ F ∈ cusp Xo c U a n, ∀ σ, GoodEmb c σ → ∀ (y : FrPt Xo c (CAt σ)) (N : ℝ), IsMetric y N (fun _ => 1) → cabs (evR Xo c F y) ≤ Real.sqrt N ^ n * supC Xo c U ξ σ a n F := by
  intro E _ _ _ H Dw l Xo c r U ξ hU hξ hpq a n hd F hF σ hσ y N hN
  have hB : Out.SecBaseChangeSt := GlobalTheory.lawsFieldsSeparately.2.1
  obtain ⟨-, -, -, -, -, -, hwt⟩ := GlobalTheory.Frames.algebraic_laws hB E H Dw l Xo c
  obtain ⟨k, x, t, hx, ht⟩ := GlobalTheory.T.exists_orthonormalFrame_borelChange_complexFramedPoint E H Dw l Xo c σ r (U σ) (hU σ hσ) y
  obtain ⟨g, hg0, hgd, hchg⟩ :=
    ((GlobalTheory.Frames.frBor_calculus E H Dw l Xo c (CAt σ) ((U σ).un k x) y y).1 t).1 ht
  have hξ0 : 0 < ξ := by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    rw [← hξ σ hσ k τ]
    exact norm_pos_iff.2 ((map_ne_zero τ).2 ((U σ).X k).ξ0_ne)
  have hκ : 0 < 2 * Real.pi * ξ := by positivity
  have hm0 := GlobalTheory.T.unif_metric_scalar E H Dw l Xo c σ r (U σ) ξ hσ (hU σ hσ) hpq k x (hξ σ hσ k) hx
  have hm1 := GlobalTheory.T.metric_change_of_frame E H Dw l Xo c σ ((U σ).un k x) y 1 _
    (fun b => Matrix.transpose (show Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) ℂ from g b))
    (show ℂ from (t none : CAt σ)) (Units.ne_zero (M₀ := ℂ) (t none)) hchg hm0
  obtain ⟨hNN, hG⟩ := GlobalTheory.T.metric_data_unique E H Dw l Xo c σ y _ _ _ _ hN hm1
  have hnone : cabs (t none : CAt σ) = Real.sqrt N := by
    rw [hNN, _root_.mul_one, Real.sqrt_sq (norm_nonneg _)]; rfl
  have hsome : ∀ p : Σ τ : E →+* ℂ, Fin (Dw.mult τ),
      cabs (t (some p) : CAt σ) = (Real.sqrt (2 * Real.pi * ξ))⁻¹ := by
    rintro ⟨τ, i⟩
    rw [← hgd τ i]
    exact norm_diag_of_triangular
      (Matrix.transpose (show Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ from g τ)) _ hκ
      (fun i j hij => hg0 τ j i hij) (congrFun hG τ).symm i
  have hev := hwt (CAt σ) (GlobalTheory.FrameNorm.Comparison₂.isReduced_cAt σ) a n F (cusp_le_sec Xo c U a n hF) t _ _ ht
  have hlie : ∏ p : Σ τ : E →+* ℂ, Fin (Dw.mult τ), (Real.sqrt (2 * Real.pi * ξ))⁻¹ ^ a (p.1, p.2) =
      lieFac Dw ξ a := by
    have hs : (Real.sqrt (2 * Real.pi * ξ))⁻¹ = Real.exp (-(1 / 2) * Real.log (2 * Real.pi * ξ)) := by
      rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hκ, ← Real.exp_neg]
      congr 1; ring
    simp only [hs, ← Real.exp_nat_mul]
    rw [← Real.exp_sum, lieFac, ← Finset.sum_mul]
    congr 1
    rw [Fintype.sum_sigma]
    ring
  have hw : cabs (wchar (ex Dw a n) t) = Real.sqrt N ^ n * lieFac Dw ξ a := by
    rw [GlobalTheory.FrameNorm.Comparison₂.cabs_wchar, Fintype.prod_option, hnone, ← hlie]
    congr 1
    exact Finset.prod_congr rfl fun p _ => by rw [hsome p]; rfl
  have hrd : ‖rdU (U σ) F k x.1‖ = cabs (evR Xo c F ((U σ).un k x)) := by
    have e : rdU (U σ) F k x.1 = toC (evR Xo c F ((U σ).un k x)) := dif_pos x.2
    rw [e]; rfl
  have hle := Formalism.L2.Pj.abelian₂.pnorm_le_supN (U σ).X (laU (U σ) a n) (rdU (U σ) F) (supE_cusp_ne_top hσ hF) k x.1 x.2
  rw [PullbackSections.PfSupAtUnit.pnorm_unit _ _ _ (PullbackSections.PfSupAtUnit.dmin_ortho _ hx), hrd] at hle
  rw [hev, GlobalTheory.FrameNorm.Comparison₂.cabs_mul, hw, supC, _root_.mul_assoc]
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hle (lieFac_pos _ _ _).le)
    (pow_nonneg (Real.sqrt_nonneg _) _)

end GlobalTheory.LamT.OrthoBound
