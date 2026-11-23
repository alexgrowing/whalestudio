import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.GroupDict
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSheetCover
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsProved
import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.Assembly
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntEmbInjective
import Development.AutomorphicSpectrum.Proofs.MetricProofs.PPartRealSmul
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsAdaptedFrameBisStatement
import GroundTheory.HeightsAndTheta.Heights.Regularisation.PosSemidefOfIntQuadNonneg
import ReciprocityTheory.AnalyticForms.AnalyticCharts.Osgood
import Development.AutomorphicSpectrum.Proofs.MetricProofs.HolomorphicEigenProjectionOnBallStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.PeriodExtensionImaginaryFormStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.EigenProjectionInEigenspaceStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.AdaptedFrameHermitianProductStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SignatureUnitaryBlocksInvertibleStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.AdaptedFrameBallCoordinateStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LinearIndependentOfGramDetUnitStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.HolomorphicCoefficientsInFrameStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BallDomainOpenConvexZeroStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BallPotentialFormulaStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogDetChangeStatement
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsSideAlt
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Chart

theorem differentiableOn_prod' {n : ℕ} {U : Set (Fin n → ℂ)} {ι : Type} (u : Finset ι) {f : ι → (Fin n → ℂ) → ℂ}
    (h : ∀ i ∈ u, DifferentiableOn ℂ (f i) U) : DifferentiableOn ℂ (fun t => ∏ i ∈ u, f i t) U :=
  _root_.UpperTheory.Reformulated.B.Yhd5.main u h

theorem differentiableOn_det' {n m : ℕ} {U : Set (Fin n → ℂ)} {M : (Fin n → ℂ) → Matrix (Fin m) (Fin m) ℂ}
    (h : ∀ a b, DifferentiableOn ℂ (fun t => M t a b) U) : DifferentiableOn ℂ (fun t => (M t).det) U := by
  simp only [Matrix.det_apply]
  refine DifferentiableOn.fun_sum fun σ _ => ?_
  refine DifferentiableOn.const_smul ?_ _
  exact differentiableOn_prod' _ fun i _ => h _ _

theorem chart_exists : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ] (j j' n g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (F : UnivFam E Ψ j j' n g Λ) (C : LatEmb F) (A₀ : Ψ → Matrix (Fin (j + j')) (Sg j j') ℂ), C.IsAdapted (F.R 0) A₀ → ∃ (Z : (Fin n → ℂ) → Fin n → ℂ) (G : (Fin n → ℂ) → ℂ), DifferentiableOn ℂ Z (ballDom F.q) ∧ DifferentiableOn ℂ G (ballDom F.q) ∧ (∀ t ∈ ballDom F.q, ∀ A, C.IsAdapted (F.R t) A → Z t = moebBall F.q (fun τ => C.cinv (A₀ τ) τ * A τ) 0) ∧ ∀ t ∈ ballDom F.q, ballPot F.q (Z t) = ballPot F.q t + (G t).re := by
  intro E _ _ _ Ψ _ j j' n g Λ _ _ F C A₀ h₀
  obtain ⟨hUo, hUc, hU0⟩ := GlobalTheory.T.ball_domain_open_convex_zero Ψ j j' n F.q
  have hunit : ∀ τ, (A₀ τ)ᴴ * C.sgr τ * A₀ τ = sgI j j' := h₀.unit
  have hex : ∀ t, ∃ A, t ∈ ballDom F.q → C.IsAdapted (F.R t) A := fun t => by
    by_cases ht : t ∈ ballDom F.q
    · obtain ⟨A, hA⟩ := GlobalTheory.T.exists_adapted_frame_bis E Ψ j j' n g Λ F C (F.R t) (F.form_eq t) (F.sig t ht)
      exact ⟨A, fun _ => hA⟩
    · exact ⟨A₀, fun h => absurd h ht⟩
  choose Ad hAd using hex

  let dV : Ψ → Fin j' → (Fin n → ℂ) → Fin g → ℂ :=
    fun τ b t => C.pPart (F.R t) τ (A₀ τ *ᵥ Sum.elim 0 (Pi.single b 1))
  let aV : Ψ → Fin j → (Fin n → ℂ) → Fin g → ℂ :=
    fun τ i t => C.pPart (F.R t) τ (A₀ τ *ᵥ Sum.elim (Pi.single i 1) 0)
  let Wm : (Fin n → ℂ) → Ψ → Matrix (Fin j') (Fin j) ℂ := fun t τ => moebW (C.cinv (A₀ τ) τ * Ad t τ) 0
  have hgA := fun t (A : Ψ → Matrix (Fin (j + j')) (Sg j j') ℂ) (hA : C.IsAdapted (F.R t) A) =>
    GlobalTheory.T.adapted_frame_hermitian_product E Ψ j j' n g Λ F C (F.R t) A (GlobalTheory.T.period_extension_imaginary_form E Ψ j j' n g Λ F C (F.R t) (F.form_eq t)) hA
  have hpt := fun t (ht : t ∈ ballDom F.q) τ =>
    GlobalTheory.T.adapted_frame_ball_coordinate E Ψ j j' n g Λ F C (F.R t) (Ad t) A₀ τ (Wm t τ) (GlobalTheory.T.signature_unitary_blocks_invertible j j') (hgA t (Ad t) (hAd t ht) τ) (hAd t ht) (hunit τ) rfl

  have hgram : ∀ t ∈ ballDom F.q, ∀ τ, IsUnit (F.R t |>.gram fun b => dV τ b t).det := by
    intro t ht τ
    have h := (hpt t ht τ).2.1
    have hc : ((2 * C.c : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (mul_pos two_pos C.c_pos).ne'
    have h2 := congrArg Matrix.det h
    rw [Matrix.det_mul, Matrix.det_smul, Matrix.det_one, mul_one] at h2
    exact isUnit_iff_ne_zero.2 (left_ne_zero_of_mul (h2 ▸ pow_ne_zero _ hc))
  have hind : ∀ t ∈ ballDom F.q, ∀ τ, LinearIndependent ℂ (fun b => dV τ b t) := fun t ht τ =>
    GlobalTheory.T.linearIndependent_of_gram_det_unit E g Λ (F.R t) j' _ (hgram t ht τ)

  have hrel : ∀ t, ∀ τ (W : Matrix (Fin j') (Fin j) ℂ),
      (∀ v : Fin j → ℂ, C.pPart (F.R t) τ (A₀ τ *ᵥ Sum.elim v (W *ᵥ v)) = 0) → ∀ i,
      -aV τ i t = ∑ b, W b i • dV τ b t := by
    intro t τ W hW i
    have h := hW (Pi.single i 1)
    rw [pPart_elim] at h
    have hWv : ∀ b, (W *ᵥ Pi.single i 1) b = W b i := by
      intro b; simp
    simp only [hWv, Pi.single_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ,
      if_true] at h
    exact (eq_neg_of_add_eq_zero_right h).symm ▸ by simp [aV, dV]

  have huniq : ∀ t ∈ ballDom F.q, ∀ τ (W W' : Matrix (Fin j') (Fin j) ℂ),
      (∀ v : Fin j → ℂ, C.pPart (F.R t) τ (A₀ τ *ᵥ Sum.elim v (W *ᵥ v)) = 0) →
      (∀ v : Fin j → ℂ, C.pPart (F.R t) τ (A₀ τ *ᵥ Sum.elim v (W' *ᵥ v)) = 0) → W = W' := by
    intro t ht τ W W' hW hW'
    ext b i
    have h1 := hrel t τ W hW i
    have h2 := hrel t τ W' hW' i
    have h3 : ∑ b, (W b i - W' b i) • dV τ b t = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib, ← h1, ← h2, sub_self]
    have := Fintype.linearIndependent_iff.1 (hind t ht τ) _ h3 b
    exact sub_eq_zero.1 this

  have hdV : ∀ τ b, DifferentiableOn ℂ (dV τ b) (ballDom F.q) := fun τ b =>
    GlobalTheory.T.holomorphic_eigen_projection_on_ball E Ψ j j' n g Λ F C τ _
  have haV : ∀ τ i, DifferentiableOn ℂ (aV τ i) (ballDom F.q) := fun τ i =>
    GlobalTheory.T.holomorphic_eigen_projection_on_ball E Ψ j j' n g Λ F C τ _

  have hWd : ∀ τ i, DifferentiableOn ℂ (fun t b => Wm t τ b i) (ballDom F.q) := fun τ i =>
    GlobalTheory.T.holomorphic_coefficients_in_frame n j' g _ (fun b => dV τ b) (fun t => -aV τ i t) (fun t b => Wm t τ b i) hUo (hdV τ) (haV τ i).neg
      (fun t ht => hind t ht τ) (fun t ht => hrel t τ _ (hpt t ht τ).1 i)

  have hY : ∀ t τ b, ∃ c : Fin j' → ℂ, t ∈ ballDom F.q → dV τ b t = ∑ i, c i • F.b τ i t := by
    intro t τ b
    by_cases ht : t ∈ ballDom F.q
    · have hm : dV τ b t ∈ Submodule.span ℂ (Set.range fun i => F.b τ i t) := by
        rw [((F.frames.2 t ht τ).2)]
        exact GlobalTheory.T.eigen_projection_in_eigenspace E Ψ j j' n g Λ F C (F.R t) τ _
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hm
      exact ⟨c, fun _ => hc.symm⟩
    · exact ⟨0, fun h => absurd h ht⟩
  choose Yc hYc using hY
  let Ym : (Fin n → ℂ) → Ψ → Matrix (Fin j') (Fin j') ℂ := fun t τ => Matrix.of fun c b => Yc t τ b c
  have hYd : ∀ τ b, DifferentiableOn ℂ (fun t => Yc t τ b) (ballDom F.q) := fun τ b =>
    GlobalTheory.T.holomorphic_coefficients_in_frame n j' g _ (F.b τ) (dV τ b) (fun t => Yc t τ b) hUo (F.frames.1 τ) (hdV τ b)
      (fun t ht => (F.frames.2 t ht τ).1) (fun t ht => hYc t τ b ht)

  have hloc := fun t (ht : t ∈ ballDom F.q) τ =>
    GlobalTheory.T.gram_det_change_of_basis_alt E g Λ (F.R t) j' (fun i => F.b τ i t) (fun b => dV τ b t) (Ym t τ) (1 - Wm t τ * (Wm t τ)ᴴ) (2 * C.c)
      (mul_pos two_pos C.c_pos) (fun b => hYc t τ b ht) (hpt t ht τ).2.1 (hpt t ht τ).2.2

  let Pf : (Fin n → ℂ) → ℂ := fun t => ∏ τ, (Ym t τ).det
  have hPd : DifferentiableOn ℂ Pf (ballDom F.q) := by
    refine differentiableOn_prod' _ fun τ _ => differentiableOn_det' fun a b => ?_
    exact (differentiableOn_pi.1 (hYd τ b)) a
  have hP0 : ∀ t ∈ ballDom F.q, Pf t ≠ 0 := fun t ht =>
    Finset.prod_ne_zero_iff.2 fun τ _ => (hloc t ht τ).1
  obtain ⟨G₀, hG₀a, hG₀⟩ := GroundTheory.Heights₂.Heights.Regular.exists_analytic_log hUo hUc ⟨0, hU0⟩
    (ReciprocityTheory.AnForm.Osgood.osgood n _ Pf hUo hPd) hP0
  have hG₀d : DifferentiableOn ℂ G₀ (ballDom F.q) := hG₀a.differentiableOn
  refine ⟨fun t => ballPt F.q (Wm t), fun t => 2 * G₀ t - ((Fintype.card Ψ * j' * Real.log (2 * C.c) : ℝ) : ℂ), ?_, ?_, ?_, ?_⟩
  · refine differentiableOn_pi.2 fun k => ?_
    exact (differentiableOn_pi.1 (hWd _ _)) _
  · exact (hG₀d.const_mul 2).sub_const _
  · intro t ht A hA
    have hb0 : ∀ τ, ballMat F.q 0 τ = 0 := fun τ => by ext a b; simp [ballMat]
    have : (fun τ => Wm t τ) = fun τ => moebW (C.cinv (A₀ τ) τ * A τ) ((ballMat F.q 0 τ)ᵀ) := by
      funext τ
      rw [hb0, Matrix.transpose_zero]
      exact huniq t ht τ _ _ (hpt t ht τ).1
        (GlobalTheory.T.adapted_frame_ball_coordinate E Ψ j j' n g Λ F C (F.R t) A A₀ τ _ (GlobalTheory.T.signature_unitary_blocks_invertible j j') (hgA t A hA τ) hA (hunit τ) rfl).1
    simp only [moebBall]
    exact congrArg (ballPt F.q) this
  · intro t ht
    have hre : (G₀ t).re = ∑ τ, Real.log ‖(Ym t τ).det‖ := by
      have h1 : ‖Pf t‖ = Real.exp (G₀ t).re := by rw [← hG₀ t ht, Complex.norm_exp]
      have h2 : Real.log ‖Pf t‖ = (G₀ t).re := by rw [h1, Real.log_exp]
      rw [← h2, norm_prod, Real.log_prod]
      intro τ _
      exact norm_ne_zero_iff.2 (hloc t ht τ).1
    rw [GlobalTheory.T.ball_potential_formula, ← F.logDet_eq t ht]
    simp only [RiemLat.logDet, ← Finset.sum_neg_distrib]
    simp only [Complex.sub_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, Complex.ofReal_re, zero_mul, sub_zero, hre]
    rw [Finset.sum_congr rfl fun τ _ => (hloc t ht τ).2]
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      ← Finset.mul_sum]
    ring

end GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Chart
