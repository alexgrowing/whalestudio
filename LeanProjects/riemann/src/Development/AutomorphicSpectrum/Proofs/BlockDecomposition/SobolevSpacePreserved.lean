import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartAndRightWordsSmooth
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatrixExpCurveDerivativeStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RegularRepresentationContinuousStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LpIntegralAePointwiseStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ApproximateIdentityExistsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MollificationDifferentiableStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MollificationRightTranslateStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MollificationEvaluationContinuousStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DerivativeRightBasisExpansionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.L2LimitEqPointwiseLimitHoldsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeftConvolutionApproximationStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MollificationAeEqConvolutionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosedDerivativeSystemSmoothStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RightTranslateDerivativeIntegralStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SobolevSequenceUniformCauchyStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformLimitRightDerivativesStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RwAppend
open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc GlobalTheory.CompanionTheory.PresSobA
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section

namespace GlobalTheory.CompanionTheory.PresSobA

variable {n : ℕ} [MeasurableSpace (G n)] [BorelSpace (G n)] {μ : Measure (G n)} [μ.IsHaarMeasure]
  {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

theorem rR_one (hU : Unimod) (y : Lp V 2 μ) : rR μ V 1 y = y := by
  apply Lp.ext
  filter_upwards [rR_coe μ hU 1 y] with z hz
  simpa using hz

theorem lT_one (y : Lp V 2 μ) : lT μ V 1 y = y := by
  apply Lp.ext
  filter_upwards [lT_coe μ 1 y] with z hz
  simpa using hz

theorem orbit_deriv (hU : Unimod) {f : Mat n → V} (X : Mat n) (hf : ContDiffOn ℝ ∞ f (GLs n))
    (h0 : MemLp (fun y : G n => f y.val) 2 μ) (h1 : MemLp (fun y : G n => Rd X f y.val) 2 μ) :
    HasDerivAt (fun t : ℝ => rR μ V (expC X t) (cls μ f)) (cls μ (Rd X f)) 0 := by
  have hc : Continuous (fun s : ℝ => rR μ V (expC X s) (cls μ (Rd X f))) :=
    (GlobalTheory.T.regular_representation_continuous n μ V hU _).1.comp (GlobalTheory.T.matrix_exp_curve_derivative n X).1
  have hd := intervalIntegral.integral_hasDerivAt_right (a := (0 : ℝ)) (b := 0)
    (hc.intervalIntegrable _ _) hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  simp only [expC_zero, rR_one hU] at hd
  have he : (fun t : ℝ => rR μ V (expC X t) (cls μ f)) =
      fun t : ℝ => (∫ s in (0 : ℝ)..t, rR μ V (expC X s) (cls μ (Rd X f))) + cls μ f := by
    funext t
    rw [← GlobalTheory.T.right_translate_derivative_integral n μ V hU f X hf h0 h1 t]
    abel
  rw [he]
  exact hd.add_const _

theorem mol_family (hU : Unimod) (x : List (Bool × Fin n × Fin n) → Lp V 2 μ)
    (hx : ∀ w p, HasDerivAt (fun t : ℝ => rR μ V (expC (bs p) t) (x w)) (x (p :: w)) 0)
    {φ : Mat n → ℝ} (hφ : IsTest φ) :
    (∀ w, ContDiffOn ℝ ∞ (Mol μ φ (⇑(x w))) (GLs n)) ∧
      ∀ w p, ∀ z ∈ GLs n, Rd (bs p) (Mol μ φ (⇑(x w))) z = Mol μ φ (⇑(x (p :: w))) z := by
  have hd : ∀ w p, ∀ z ∈ GLs n, Rd (bs p) (Mol μ φ (⇑(x w))) z = Mol μ φ (⇑(x (p :: w))) z := by
    intro w p z hz
    obtain ⟨Lz, hL⟩ := GlobalTheory.T.mollification_evaluation_continuous n μ V hU φ hφ z hz
    have h1 : HasDerivAt (fun t : ℝ => Lz (rR μ V (expC (bs p) t) (x w))) (Lz (x (p :: w))) 0 :=
      Lz.hasFDerivAt.comp_hasDerivAt 0 (hx w p)
    have hcur : HasDerivAt (fun t : ℝ => z * (expC (bs p) t).val) (z * bs p) 0 := by
      have h0 := (GlobalTheory.T.matrix_exp_curve_derivative n (bs p)).2 0
      rw [expC_zero] at h0
      simp only [Units.val_one, one_mul] at h0
      exact (LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℝ z) : Mat n →L[ℝ] Mat n).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h0
    have hdiff := (GlobalTheory.T.mollification_differentiable n μ V hU φ hφ (x w) z hz).hasFDerivAt
    have h2 : HasDerivAt (fun t : ℝ => Mol μ φ (⇑(x w)) (z * (expC (bs p) t).val))
        (fderiv ℝ (Mol μ φ (⇑(x w))) z (z * bs p)) 0 := by
      have hz0 : z * (expC (bs p) 0).val = z := by simp [expC_zero]
      have hdiff' : HasFDerivAt (Mol μ φ (⇑(x w))) (fderiv ℝ (Mol μ φ (⇑(x w))) z)
          (z * (expC (bs p) 0).val) := by rw [hz0]; exact hdiff
      exact hdiff'.comp_hasDerivAt 0 hcur
    have h3 : (fun t : ℝ => Lz (rR μ V (expC (bs p) t) (x w))) =
        fun t : ℝ => Mol μ φ (⇑(x w)) (z * (expC (bs p) t).val) := by
      funext t
      rw [hL, GlobalTheory.T.mollification_right_translate n μ V hU]
    rw [h3] at h1
    rw [← hL]
    exact h2.unique h1
  refine ⟨fun w => ?_, hd⟩
  exact GlobalTheory.T.closed_derivative_system_smooth n V (List (Bool × Fin n × Fin n)) (fun w => Mol μ φ (⇑(x w))) (fun p w => p :: w)
    (fun w z hz => GlobalTheory.T.mollification_differentiable n μ V hU φ hφ (x w) z hz) (fun w p z hz => hd w p z hz) w

theorem limit_sob (hS : SobG) (g : ℕ → Mat n → V) (x : List (Bool × Fin n × Fin n) → Lp V 2 μ)
    (hg : ∀ k, ContDiffOn ℝ ∞ (g k) (GLs n)) (hm : ∀ k w, MemLp (fun y : G n => Rw w (g k) y.val) 2 μ)
    (hx : ∀ w, Tendsto (fun k => cls μ (Rw w (g k))) atTop (𝓝 (x w))) :
    ∃ f', Sob μ f' ∧ ∀ w, cls μ (Rw w f') = x w := by
  obtain ⟨Gf, hu, hc, hw⟩ := GlobalTheory.T.uniform_limit_right_derivatives n V g hg (GlobalTheory.T.sobolev_sequence_uniform_cauchy hS n μ V g x hg hm hx)
  have key : ∀ w, MemLp (fun y : G n => Rw w (Gf []) y.val) 2 μ ∧ cls μ (Rw w (Gf [])) = x w := by
    intro w
    refine GlobalTheory.T.l2_limit_eq_pointwise_limit_holds n μ V (fun k => Rw w (g k)) (Rw w (Gf [])) (x w) (fun k => hm k w) (hx w) ?_
    intro z hz
    rw [hw w z hz]
    exact (hu w).tendsto_at hz
  exact ⟨Gf [], ⟨hc, fun w => (key w).1⟩, fun w => (key w).2⟩

end GlobalTheory.CompanionTheory.PresSobA

open GlobalTheory.CompanionTheory.PresSobA in

theorem GlobalTheory.CompanionTheory.PresSobA.presSob : PresSob := by
  intro n _ _ μ _ V _ _ _ S hLg hU hRC hS hcomm f hf
  have hsob : ∀ w, ContDiffOn ℝ ∞ (Rw w f) (GLs n) := fun w => GlobalTheory.CompanionTheory.SobGL.Smooth.Rw_contDiffOn' hf.1 w
  set x : List (Bool × Fin n × Fin n) → Lp V 2 μ := fun w => S (cls μ (Rw w f)) with hxdef
  have hx : ∀ w p, HasDerivAt (fun t : ℝ => rR μ V (expC (bs p) t) (x w)) (x (p :: w)) 0 := by
    intro w p
    have h1 := orbit_deriv (μ := μ) hU (bs p) (hsob w) (hf.2 w) (hf.2 (p :: w))
    have h2 : HasDerivAt (fun t : ℝ => (S.restrictScalars ℝ) (rR μ V (expC (bs p) t) (cls μ (Rw w f))))
        ((S.restrictScalars ℝ) (cls μ (Rd (bs p) (Rw w f)))) 0 :=
      (S.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 h1
    have h3 : (fun t : ℝ => rR μ V (expC (bs p) t) (x w)) =
        fun t : ℝ => (S.restrictScalars ℝ) (rR μ V (expC (bs p) t) (cls μ (Rw w f))) := by
      funext t
      exact (DFunLike.congr_fun (hcomm (expC (bs p) t)) _).symm
    rw [h3]
    exact h2
  obtain ⟨φ, hφ, hφ0, hφ1, hφs⟩ := GlobalTheory.T.approximate_identity_exists n μ
  have hfam := fun k => mol_family (μ := μ) hU x hx (hφ k)
  have hRw : ∀ k w, ∀ z ∈ GLs n, Rw w (Mol μ (φ k) (⇑(x []))) z = Mol μ (φ k) (⇑(x w)) z := by
    intro k w
    induction w with
    | nil => exact fun z _ => rfl
    | cons p w ih =>
      intro z hz
      exact (Rd_congr ih (bs p) z hz).trans ((hfam k).2 w p z hz)
  have hae : ∀ k w, (fun y : G n => Rw w (Mol μ (φ k) (⇑(x []))) y.val) =ᵐ[μ] lConv μ V (φ k) (x w) := by
    intro k w
    have h0 : (fun y : G n => Rw w (Mol μ (φ k) (⇑(x []))) y.val) = fun y : G n => Mol μ (φ k) (⇑(x w)) y.val :=
      funext fun y => hRw k w y.val (by
        have := (Matrix.isUnit_iff_isUnit_det _).1 y.isUnit
        exact this.ne_zero)
    rw [h0]
    exact GlobalTheory.T.mollification_ae_eq_convolution n μ V hU (φ k) (hφ k) (x w)
  have hlim : ∀ w, Tendsto (fun k => cls μ (Rw w (Mol μ (φ k) (⇑(x []))))) atTop (𝓝 (x w)) := by
    intro w
    have : (fun k => cls μ (Rw w (Mol μ (φ k) (⇑(x []))))) = fun k => lConv μ V (φ k) (x w) :=
      funext fun k => (cls_of_ae μ (hae k w)).2
    rw [this, Metric.tendsto_nhds]
    intro ε hε
    have hc : Continuous (fun y : G n => lT μ V y (x w)) := (GlobalTheory.T.regular_representation_continuous n μ V hU _).2
    have h1 : {y : G n | dist (lT μ V y (x w)) (x w) < ε / 2} ∈ 𝓝 (1 : G n) := by
      have h2 := (hc.tendsto (1 : G n))
      rw [lT_one] at h2
      exact h2 (Metric.ball_mem_nhds _ (half_pos hε))
    filter_upwards [hφs _ h1] with k hk
    have h3 := GlobalTheory.T.left_convolution_approximation n μ V hU (φ k) (hφ k) (hφ0 k) (hφ1 k) (x w) (ε / 2)
      (fun y hy => by
        have h4 := hk y hy
        rw [dist_eq_norm] at h4
        exact h4.le)
    rw [dist_eq_norm]
    linarith
  obtain ⟨f', hf', hcl⟩ := limit_sob (μ := μ) hS (fun k => Mol μ (φ k) (⇑(x []))) x (fun k => (hfam k).1 [])
    (fun k w => (cls_of_ae μ (hae k w)).1) hlim
  exact ⟨f', hf', hcl [], hcl⟩
