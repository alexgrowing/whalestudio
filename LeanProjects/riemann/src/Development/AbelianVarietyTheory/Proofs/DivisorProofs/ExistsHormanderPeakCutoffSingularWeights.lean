import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.KaUnfoldPfC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfM
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.DifferentiableChart
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FirstMinimumInvariantContinuousPosOnFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormFactorAndDensityNearOneInFlagChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramChartSubFormEntryLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartBallWeightPotentialDensityBoundsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UpperTriangularNearUnitDiagonalOfTwistedGramNearStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusStrictLowerComparisonNearIdentityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviFormsTransportToOrthonormalChartOriginStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviMarginOrthonormalChartOriginStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviFormCutoffLogWeightLowerBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarDerivCutoffNormSqBoundAnnulusStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartBallExtendByZeroInvariantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyNotMemChartBallSaturationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantExtensionMeasurableContDiffOnChartStatement

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.PeakWeight

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem low_apply (X : Data E r) (w : V (nd X)) (τ : X.Ψ) (a c : Fin r) :
    (mat (nmat X w) τ - 1) a c =
      if h : c < a then w ((Fintype.equivFin (Ent X)) ⟨τ, ⟨(a, c), h⟩⟩) else 0 := by
  simp only [mat, nmat, Matrix.sub_apply, Matrix.of_apply, Matrix.one_apply]
  by_cases h : c < a
  · simp [h, h.ne']
  · simp [h]

theorem sum_entries (X : Data E r) (ξ : Fin (nd X) → ℂ) :
    ∑ j, ‖ξ j‖ ^ 2 = ∑ τ, ∑ a, ∑ c, ‖(mat (nmat X (WithLp.toLp 2 ξ)) τ - 1) a c‖ ^ 2 := by
  have e : ∑ j, ‖ξ j‖ ^ 2 = ∑ e : Ent X, ‖ξ (Fintype.equivFin (Ent X) e)‖ ^ 2 :=
    ((Fintype.equivFin (Ent X)).sum_comp (fun j => ‖ξ j‖ ^ 2)).symm
  rw [e, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun τ _ => ?_
  have h2 : ∀ a c : Fin r, ‖(mat (nmat X (WithLp.toLp 2 ξ)) τ - 1) a c‖ ^ 2 =
      if c < a then ‖(mat (nmat X (WithLp.toLp 2 ξ)) τ - 1) a c‖ ^ 2 else 0 := by
    intro a c
    split_ifs with h
    · rfl
    · rw [low_apply, dif_neg h]; simp
  rw [Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => h2 a c,
    ← Fintype.sum_prod_type' (f := fun a c : Fin r =>
      if c < a then ‖(mat (nmat X (WithLp.toLp 2 ξ)) τ - 1) a c‖ ^ 2 else 0), ← Finset.sum_filter,
    Finset.sum_subtype (p := fun p : Fin r × Fin r => p.2 < p.1) _ (by simp)]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [low_apply, dif_pos y.2]

theorem levi_ball (X : Data E r) {x : Frame X.Ψ r} (hx : IsOrth X x) (hr : 0 < r) {z : V (nd X)}
    (hz : ‖z‖ ≤ 1 / (100 * (r : ℝ) ^ 2)) (ξ : Fin (nd X) → ℂ) :
    ∃ (x1 : Frame X.Ψ r) (ξ' : Fin (nd X) → ℂ), IsOrth X x1 ∧
      (∀ la : Wt X.Ψ r, leviM X (phla X la) x z ξ = leviM X (phla X la) x1 0 ξ') ∧
      ∑ j, ‖ξ j‖ ^ 2 ≤ 2 * ∑ j, ‖ξ' j‖ ^ 2 := by
  have hzO : z ∈ OmF X x := (GlobalTheory.T.chartBall_weightPotential_density_bounds E r X 0 x z hx hz).1
  obtain ⟨x1, ho, b, hb, hxb⟩ := ortho_holds r X _ hzO
  obtain ⟨ξ', h1, B, hB, hrel⟩ := GlobalTheory.T.leviForms_transport_to_orthonormal_chart_origin E r X x x1 b z ho hzO hb hxb ξ
  refine ⟨x1, ξ', ho, h1, ?_⟩
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hδ : (r : ℝ) * ‖z‖ ≤ 1 / 100 := by
    rw [le_div_iff₀ (by positivity)] at hz
    nlinarith [mul_nonneg (norm_nonneg z) (mul_nonneg (sub_nonneg.2 hr1) (by positivity : (0 : ℝ) ≤ r))]
  rw [sum_entries, sum_entries, Finset.mul_sum]
  refine Finset.sum_le_sum fun τ _ => ?_
  have hu : IsUnit (mat x1 τ).det := isUnit_iff_ne_zero.mpr ((IW.orth_mem_dom X x1 ho) τ).1
  have hm : mat x τ * mat (nmat X z) τ = mat x1 τ * mat b τ := congrFun hxb τ
  have hG : (mat b τ)ᵀ * PoinPf.Jd X * (mat b τ).map (starRingEnd ℂ) = PoinPf.Gw X z τ := by
    have := congrArg (gram τ.1 X.Gm) hm
    rw [FrameDegreeData.gram_mul, FrameDegreeData.gram_mul, hx τ, ho τ] at this
    exact this.symm
  obtain ⟨hd, hoff⟩ := GlobalTheory.T.upperTriangular_near_unitDiagonal_of_twistedGram_near r (fun a => sgn X.p0 a) (mat b τ) ‖z‖
    (fun a => by unfold sgn; split_ifs <;> simp) (norm_nonneg _) hδ (hb τ).2 (fun a c => by
      have := GlobalTheory.GramChartNear.gw_sub_jd_le E r X z τ a c (by linarith)
      rw [← hG] at this
      exact this)
  refine GlobalTheory.T.frobenius_strictLower_comparison_near_identity r ((mat x1 τ)⁻¹ * mat x τ) (mat (nmat X z) τ) (mat b τ) (mat B τ) _ _ ‖z‖
    (norm_nonneg _) hδ (fun a c h => ?_) (fun a => ?_) (fun a c h => ?_) (hb τ).2 hd hoff (hB τ)
    (fun a c h => ?_) (fun a c h => ?_) ?_ ?_
  · simp [mat, nmat, not_lt.2 h.le, h.ne]
  · simp [mat, nmat]
  · have := GlobalTheory.ChartNearOne.nmat_entry_le X z τ a c
    rwa [if_neg h.ne', sub_zero] at this
  · rw [low_apply, dif_neg (not_lt.2 h)]
  · rw [low_apply, dif_neg (not_lt.2 h)]
  · rw [Matrix.mul_assoc, hm, Matrix.nonsing_inv_mul_cancel_left _ _ hu]
  · rw [Matrix.mul_assoc, hrel τ, Matrix.nonsing_inv_mul_cancel_left _ _ hu]

def smoothLevi (X : Data E r) (la : Wt X.Ψ r) (bb : ℝ) (x : Frame X.Ψ r) (z : V (nd X))
    (ξ : Fin (nd X) → ℂ) : ℝ :=
  leviM X (phla X la) x z ξ - bb * leviM X (phla X (GlobalTheory.CurvMargin.blockWt X)) x z ξ -
    leviM X (phla X (kapW X)) x z ξ

theorem weight_eventually (X : Data E r) {x : Frame X.Ψ r} (hx : IsOrth X x) (la : Wt X.Ψ r) (bb : ℝ)
    (ψ : Frame X.Ψ r → ℝ) {z : V (nd X)} (hz : z ∈ OmF X x) :
    (fun w => phla X la (cpt X x w) - bb * rhF X x w - Real.log (densF X x w) + ψ (cpt X x w)) =ᶠ[𝓝 z]
      fun w => phla X la (cpt X x w) + ((-bb) * phla X (GlobalTheory.CurvMargin.blockWt X) (cpt X x w) +
        ((-1) * phla X (kapW X) (cpt X x w) + ψ (cpt X x w))) := by
  filter_upwards [(ExF.isOpen_OmF X x).mem_nhds hz] with w hw
  rw [GlobalTheory.CurvMargin.phla_blockWt_cpt X x hx hw, IW.phla_kapW_cpt X x hx hw]
  ring

theorem weight_smooth (X : Data E r) {x : Frame X.Ψ r} (hx : IsOrth X x) (la : Wt X.Ψ r) (bb : ℝ)
    {ψ : Frame X.Ψ r → ℝ} (hψ : ContDiffOn ℝ ∞ (fun w => ψ (cpt X x w)) (OmF X x)) :
    ContDiffOn ℝ ∞ (fun w => phla X la (cpt X x w) - bb * rhF X x w - Real.log (densF X x w) +
      ψ (cpt X x w)) (OmF X x) := by
  intro z hz
  refine ContDiffAt.contDiffWithinAt (ContDiffAt.congr_of_eventuallyEq ?_ (weight_eventually X hx la bb ψ hz))
  exact (IW.phla_cpt_cdAt X x hz _).add ((contDiffAt_const.mul (IW.phla_cpt_cdAt X x hz _)).add
    ((contDiffAt_const.mul (IW.phla_cpt_cdAt X x hz _)).add
      (hψ.contDiffAt ((ExF.isOpen_OmF X x).mem_nhds hz))))

theorem weight_levi (X : Data E r) {x : Frame X.Ψ r} (hx : IsOrth X x) (la : Wt X.Ψ r) (bb : ℝ)
    {ψ : Frame X.Ψ r → ℝ} (hψ : ContDiffOn ℝ ∞ (fun w => ψ (cpt X x w)) (OmF X x))
    {z : V (nd X)} (hz : z ∈ OmF X x) (ξ : Fin (nd X) → ℂ) :
    (leviV (nd X) (fun w => ((phla X la (cpt X x w) - bb * rhF X x w - Real.log (densF X x w) +
      ψ (cpt X x w) : ℝ) : ℂ)) z ξ).re = smoothLevi X la bb x z ξ + leviM X ψ x z ξ := by
  have hev : (fun w => ((phla X la (cpt X x w) - bb * rhF X x w - Real.log (densF X x w) +
      ψ (cpt X x w) : ℝ) : ℂ)) =ᶠ[𝓝 z] fun w => ((phla X la (cpt X x w) +
        ((-bb) * phla X (GlobalTheory.CurvMargin.blockWt X) (cpt X x w) +
        ((-1) * phla X (kapW X) (cpt X x w) + ψ (cpt X x w))) : ℝ) : ℂ) := by
    filter_upwards [weight_eventually X hx la bb ψ hz] with w hw
    rw [hw]
  have h1 := (IW.phla_cpt_cdAt X x hz la).of_le HE.two_le_inf
  have h2 := (IW.phla_cpt_cdAt X x hz (GlobalTheory.CurvMargin.blockWt X)).of_le HE.two_le_inf
  have h3 := (IW.phla_cpt_cdAt X x hz (kapW X)).of_le HE.two_le_inf
  have h4 := (hψ.contDiffAt ((ExF.isOpen_OmF X x).mem_nhds hz)).of_le HE.two_le_inf
  rw [leviV_congr hev, Y.LocalMaximumSecondDerivative.leviV_ofReal_add h1
      ((contDiffAt_const.mul h2).add ((contDiffAt_const.mul h3).add h4)),
    Y.LocalMaximumSecondDerivative.leviV_ofReal_add (contDiffAt_const.mul h2) ((contDiffAt_const.mul h3).add h4),
    Y.LocalMaximumSecondDerivative.leviV_ofReal_add (contDiffAt_const.mul h3) h4,
    Y.LocalMaximumSecondDerivative.leviV_ofReal_const_mul _ h2, Y.LocalMaximumSecondDerivative.leviV_ofReal_const_mul _ h3]
  simp only [Complex.add_re, Complex.re_ofReal_mul, leviM, smoothLevi]
  ring

theorem leviM_phla_lact (X : Data E r) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) (la : Wt X.Ψ r)
    (x : Frame X.Ψ r) (z : V (nd X)) (ξ : Fin (nd X) → ℂ) :
    leviM X (phla X la) (lact γ x) z ξ = leviM X (phla X la) x z ξ := by
  simp only [leviM, KU.cpt_lact, phla, Data.nfac, KU.dmin_lact X hγ]

theorem nd_le (X : Data E r) : (nd X : ℝ) ≤ (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 := by
  have h : nd X ≤ X.Ψ.card * r ^ 2 := by
    unfold nd
    rw [Fintype.card_prod, Fintype.card_coe]
    refine Nat.mul_le_mul_left _ ((Fintype.card_subtype_le _).trans ?_)
    simp [sq]
  exact_mod_cast h

theorem one_le_card (X : Data E r) : (1 : ℝ) ≤ (X.Ψ.card : ℝ) := by
  have h := QuadraticCoefficientForms.card_Psi X
  rw [Fintype.card_coe] at h
  rw [h]
  exact one_le_field_half_degree

theorem levi_lower (X : Data E r) {x : Frame X.Ψ r} (hx : IsOrth X x) (hp0 : 0 < X.p0) (hp1 : X.p0 < r)
    (la : Wt X.Ψ r) {g bb K M ρ : ℝ} (hg : 0 ≤ g) (hbb : 0 ≤ bb) (hK : 0 ≤ K) (hM : 0 ≤ M)
    (hm : 2 * (K + M) ≤ g - bb - 2 * r) (hρ : ρ < 1 / (100 * (r : ℝ) ^ 2))
    (h1 : ∀ τ (a b : Fin r), (b : ℕ) = a + 1 → (b : ℕ) ≠ X.p0 → g ≤ (la τ a : ℝ) - la τ b)
    (h2 : ∀ τ (a b : Fin r), (a : ℕ) = 0 → (b : ℕ) = r - 1 → g ≤ (la τ b : ℝ) - la τ a)
    {η : V (nd X) → ℝ} {ψ : Frame X.Ψ r → ℝ}
    (hη : ∀ z (ξ : Fin (nd X) → ℂ), -(K * ∑ j, ‖ξ j‖ ^ 2) ≤ (leviV (nd X) (fun w => ((η w : ℝ) : ℂ)) z ξ).re)
    (ha : ∀ γ ∈ X.Γ, ∀ b ∈ Bor X.Ψ r, ∀ z : V (nd X), ‖z‖ ≤ 1 / (100 * (r : ℝ) ^ 2) →
      ψ (lact γ (rmul (cpt X x z) b)) = η z)
    (hb : ∀ y, (¬ ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, ∃ z : V (nd X), ‖z‖ ≤ ρ ∧
      y = lact γ (rmul (cpt X x z) b)) → ψ y = 0)
    (hl : ∀ γ ∈ X.Γ, ∀ y, ψ (lact γ y) = ψ y) (hr' : ∀ y, ∀ b ∈ Bor X.Ψ r, ψ (rmul y b) = ψ y)
    (hs : ContDiffOn ℝ ∞ (fun w => ψ (cpt X x w)) (OmF X x)) :
    (∀ z : V (nd X), ‖z‖ < 1 / (100 * (r : ℝ) ^ 2) → ∀ ξ : Fin (nd X) → ℂ,
      M * ∑ j, ‖ξ j‖ ^ 2 ≤ smoothLevi X la bb x z ξ + leviM X ψ x z ξ) ∧
    ∀ z ∈ OmF X x, ∀ ξ : Fin (nd X) → ℂ, 0 ≤ smoothLevi X la bb x z ξ + leviM X ψ x z ξ := by
  have hr : 0 < r := hp0.trans hp1
  have hdom : ∀ z : V (nd X), ‖z‖ ≤ 1 / (100 * (r : ℝ) ^ 2) → z ∈ OmF X x := fun z hz =>
    (GlobalTheory.T.chartBall_weightPotential_density_bounds E r X 0 x z hx hz).1
  have hball : ∀ z : V (nd X), ‖z‖ < 1 / (100 * (r : ℝ) ^ 2) → ∀ ξ : Fin (nd X) → ℂ,
      M * ∑ j, ‖ξ j‖ ^ 2 ≤ smoothLevi X la bb x z ξ + leviM X ψ x z ξ := by
    intro z hz ξ
    obtain ⟨x1, ξ', ho, e, hle⟩ := levi_ball X hx hr hz.le ξ
    have hO := GlobalTheory.T.leviMargin_orthonormal_chart_origin E r X la x1 g bb hp0 hp1 ho hg hbb h1 h2 ξ'
    have hev : (fun w => ((ψ (cpt X x w) : ℝ) : ℂ)) =ᶠ[𝓝 z] fun w => ((η w : ℝ) : ℂ) := by
      filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hz] with w hw
      have := ha 1 X.Γ.one_mem _ (ExtFPf.oneF_mem X) w (le_of_lt hw)
      rw [ExtFPf.rmul_oneF, KU.lact_one] at this
      rw [this]
    have hψ : leviM X ψ x z ξ = (leviV (nd X) (fun w => ((η w : ℝ) : ℂ)) z ξ).re := by
      rw [leviM, leviV_congr hev]
    have h3 := hη z ξ
    have hS : 0 ≤ ∑ j, ‖ξ j‖ ^ 2 := by positivity
    have hS' : 0 ≤ ∑ j, ‖ξ' j‖ ^ 2 := by positivity
    rw [smoothLevi, e, e, e, hψ]
    nlinarith [mul_le_mul_of_nonneg_right hm hS', mul_le_mul_of_nonneg_left hle (add_nonneg hK hM)]
  refine ⟨hball, fun z hz ξ => ?_⟩
  by_cases hc : ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, ∃ z' : V (nd X), ‖z'‖ ≤ ρ ∧
      cpt X x z = lact γ (rmul (cpt X x z') b)
  · obtain ⟨γ, hγ, b, hbB, z1, hz1, e⟩ := hc
    have hz1' := hz1.trans_lt hρ
    have hz1O := hdom z1 hz1'.le
    have e' : cpt X x z = rmul (cpt X (lact γ x) z1) b := by
      rw [e, KU.cpt_lact, KU.lact_rmul']
    obtain ⟨ξ', e1, e2⟩ := GlobalTheory.InterpCompare.levi_transport X (KU.isOrth_lact X hγ hx) hz
      (by rw [KU.OmF_lact X hγ]; exact hz1O) hbB e' ξ
    have hfun : (fun w => ψ (cpt X (lact γ x) w)) = fun w => ψ (cpt X x w) := by
      funext w; rw [KU.cpt_lact, hl γ hγ]
    have e3 := e2 ψ (fun γ' hγ' y _ b' hb' => by rw [hl γ' hγ', hr' y b' hb'])
      (by
        rw [hfun]
        exact (hs.contDiffAt ((ExF.isOpen_OmF X x).mem_nhds hz1O)).of_le HE.two_le_inf)
    have e4 : leviM X ψ (lact γ x) z1 ξ' = leviM X ψ x z1 ξ' := by
      simp only [leviM, KU.cpt_lact, hl γ hγ]
    have := hball z1 hz1' ξ'
    rw [smoothLevi] at this ⊢
    rw [e1, e1, e1, e3, e4, leviM_phla_lact X hγ, leviM_phla_lact X hγ, leviM_phla_lact X hγ]
    exact le_trans (by positivity) this
  · have hev := GlobalTheory.T.eventually_not_mem_chartBall_saturation E r X x ρ (fun w hw => hdom w (hw.trans hρ.le)) _ hz hc
    have hev' : (fun w => ((ψ (cpt X x w) : ℝ) : ℂ)) =ᶠ[𝓝 z] fun _ => (((0 : ℝ) : ℝ) : ℂ) := by
      filter_upwards [(IW.cpt_diff X x).continuous.continuousAt.eventually hev] with w hw
      rw [hb _ hw]
    have hψ : leviM X ψ x z ξ = 0 := by
      rw [leviM, leviV_congr hev']
      have : ∀ k, wdb (nd X) k (fun _ : V (nd X) => (((0 : ℝ) : ℝ) : ℂ)) = fun _ => 0 := by
        intro k; funext y; simp [wdb]
      simp only [leviV, this]
      simp [wd]
    obtain ⟨x1, ho, b, hbB, hxb⟩ := ortho_holds r X _ hz
    obtain ⟨ξ', e, -⟩ := GlobalTheory.T.leviForms_transport_to_orthonormal_chart_origin E r X x x1 b z ho hz hbB hxb ξ
    have hO := GlobalTheory.T.leviMargin_orthonormal_chart_origin E r X la x1 g bb hp0 hp1 ho hg hbb h1 h2 ξ'
    rw [smoothLevi, e, e, e, hψ, add_zero]
    exact le_trans (mul_nonneg (by linarith) (by positivity)) hO

theorem annulus_integral (X : Data E r) (x : Frame X.Ψ r) {ρ M : ℝ} (hM : 0 ≤ M) {φ : V (nd X) → ℝ}
    (h : ∀ z : V (nd X), ρ / 2 ≤ ‖z‖ → ‖z‖ < ρ → Real.exp (-φ z) ≤ M * densF X x z) :
    ∫⁻ z in OmF X x, {w : V (nd X) | ρ / 2 ≤ ‖w‖ ∧ ‖w‖ < ρ}.indicator (fun _ => (1 : ℝ≥0∞)) z *
        ENNReal.ofReal (Real.exp (-φ z)) ≤
      ENNReal.ofReal M * muF X x (Metric.ball 0 ρ ∩ OmF X x) := by
  have hO : MeasurableSet (OmF X x) := (ExF.isOpen_OmF X x).measurableSet
  have hB : MeasurableSet (Metric.ball (0 : V (nd X)) ρ ∩ OmF X x) := measurableSet_ball.inter hO
  rw [muF, withDensity_apply _ hB, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ← lintegral_indicator hB]
  refine setLIntegral_mono' hO fun z hz => ?_
  by_cases hz' : ρ / 2 ≤ ‖z‖ ∧ ‖z‖ < ρ
  · rw [Set.indicator_of_mem (by exact hz'), Set.indicator_of_mem (show z ∈ Metric.ball (0 : V (nd X)) ρ ∩ OmF X x from ⟨mem_ball_zero_iff.2 hz'.2, hz⟩), one_mul,
      ← ENNReal.ofReal_mul hM]
    exact ENNReal.ofReal_le_ofReal (h z hz'.1 hz'.2)
  · rw [Set.indicator_of_notMem (by exact hz'), zero_mul]
    exact zero_le

theorem pole {n : ℕ} {ρ c : ℝ} (hρ : 0 < ρ) (hc : 0 ≤ c) (w : V n) (u : ℕ → ℝ)
    (hu : ∀ k : ℕ, c * Real.exp (-(n * Real.log ((‖w‖ ^ 2 / ρ ^ 2 + 1 / ((k : ℝ) + 1)) / 2))) ≤ u k) :
    ENNReal.ofReal (c * ρ ^ (2 * n) * ‖w‖ ^ (-(2 * (n : ℝ)))) ≤ ⨆ k, ENNReal.ofReal (u k) := by
  by_cases hw : w = 0
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · refine le_trans (ENNReal.ofReal_le_ofReal ?_) (le_iSup (fun k => ENNReal.ofReal (u k)) 0)
      simpa using hu 0
    · have : (-(2 * (n : ℝ))) ≠ 0 := by
        have : (0 : ℝ) < n := by exact_mod_cast hn
        linarith
      rw [hw, norm_zero, Real.zero_rpow this, mul_zero, ENNReal.ofReal_zero]
      exact zero_le
  · have hw' : 0 < ‖w‖ := norm_pos_iff.2 hw
    have ht : 0 < ‖w‖ ^ 2 / ρ ^ 2 := by positivity
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt ht
    refine le_trans (ENNReal.ofReal_le_ofReal (le_trans ?_ (hu k))) (le_iSup (fun k => ENNReal.ofReal (u k)) k)
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hc
    have hlog : Real.log ((‖w‖ ^ 2 / ρ ^ 2 + 1 / ((k : ℝ) + 1)) / 2) ≤ Real.log (‖w‖ ^ 2 / ρ ^ 2) :=
      Real.log_le_log (by positivity) (by linarith)
    have e : ρ ^ (2 * n) * ‖w‖ ^ (-(2 * (n : ℝ))) = Real.exp (-(n * Real.log (‖w‖ ^ 2 / ρ ^ 2))) := by
      rw [← Real.log_pow, Real.exp_neg, Real.exp_log (by positivity), Real.rpow_neg hw'.le,
        show (2 * (n : ℝ)) = ((2 * n : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast, div_pow, ← pow_mul,
        ← pow_mul]
      field_simp
    rw [e]
    refine Real.exp_le_exp.2 (neg_le_neg (mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg n)))

theorem muF_ball_lt_top (X : Data E r) {x : Frame X.Ψ r} (hx : IsOrth X x) :
    muF X x (Metric.ball 0 (1 / (100 * (r : ℝ) ^ 2)) ∩ OmF X x) < ⊤ := by
  have hO : MeasurableSet (OmF X x) := (ExF.isOpen_OmF X x).measurableSet
  have hB : MeasurableSet (Metric.ball (0 : V (nd X)) (1 / (100 * (r : ℝ) ^ 2)) ∩ OmF X x) :=
    measurableSet_ball.inter hO
  rw [muF, withDensity_apply _ hB]
  refine lt_of_le_of_lt (setLIntegral_mono' (g := fun _ => ENNReal.ofReal (Real.exp ((X.Ψ.card : ℝ) * r))) hB
    fun z hz => ?_) ?_
  · obtain ⟨-, -, -, h1, h2⟩ := GlobalTheory.T.chartBall_weightPotential_density_bounds E r X 0 x z hx (mem_ball_zero_iff.1 hz.1).le
    refine ENNReal.ofReal_le_ofReal ?_
    rw [← Real.exp_log h2]
    exact Real.exp_le_exp.2 (abs_le.1 h1).2
  · rw [setLIntegral_const]
    refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
    exact ((Measure.restrict_apply_le _ _).trans (measure_mono Set.inter_subset_left)).trans_lt
      measure_ball_lt_top

theorem exists_cutoff : ∃ (χ : ℝ → ℝ) (A : ℝ), 0 ≤ A ∧ ContDiff ℝ ∞ χ ∧ (∀ t, 0 ≤ χ t ∧ χ t ≤ 1) ∧ (∀ t, t ≤ 1 / 4 → χ t = 1) ∧ (∀ t, 1 ≤ t → χ t = 0) ∧ (∀ t, |deriv χ t| ≤ A) ∧ (∀ t, |deriv (deriv χ) t| ≤ A) := by
  set χ : ℝ → ℝ := fun t => Real.smoothTransition ((1 - t) * (4 / 3)) with hχ
  have hs : ContDiff ℝ ∞ χ :=
    Real.smoothTransition.contDiff.comp ((contDiff_const.sub contDiff_id).mul contDiff_const)
  have h1 : ∀ t, t ≤ 1 / 4 → χ t = 1 := fun t ht => Real.smoothTransition.one_of_one_le (by linarith)
  have h0 : ∀ t, 1 ≤ t → χ t = 0 := fun t ht => Real.smoothTransition.zero_of_nonpos (by linarith)
  have hc : HasCompactSupport (deriv χ) := by
    refine HasCompactSupport.intro (isCompact_Icc (a := (1 / 4 : ℝ)) (b := 1)) fun t ht => ?_
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at ht
    rcases ht with ht | ht
    · have : χ =ᶠ[𝓝 t] fun _ => 1 := by
        filter_upwards [Iio_mem_nhds ht] with s hs' using h1 s (le_of_lt hs')
      rw [this.deriv_eq, deriv_const]
    · have : χ =ᶠ[𝓝 t] fun _ => 0 := by
        filter_upwards [Ioi_mem_nhds ht] with s hs' using h0 s (le_of_lt hs')
      rw [this.deriv_eq, deriv_const]
  have hs1 : ContDiff ℝ ∞ (deriv χ) := (contDiff_infty_iff_deriv.1 hs).2
  have hs2 : ContDiff ℝ ∞ (deriv (deriv χ)) := (contDiff_infty_iff_deriv.1 hs1).2
  obtain ⟨A1, hA1⟩ := hs1.continuous.bounded_above_of_compact_support hc
  obtain ⟨A2, hA2⟩ := hs2.continuous.bounded_above_of_compact_support hc.deriv
  refine ⟨χ, max A1 A2, (norm_nonneg _).trans ((hA1 0).trans (le_max_left _ _)), hs,
    fun t => ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩, h1, h0,
    fun t => (hA1 t).trans (le_max_left _ _), fun t => (hA2 t).trans (le_max_right _ _)⟩

theorem margin_num {A D f r T ρ : ℝ} (hA : 0 ≤ A) (hρ2 : 1 / ρ ^ 2 = 40000 * r ^ 4) (hD : D ≤ f * r ^ 2)
    (n1 : 1 ≤ T) (n2 : r ≤ T) (n4 : f * r ^ 2 ≤ T) (n6 : f * r ^ 2 * r ^ 4 ≤ T) (n7 : r ^ 4 ≤ T) :
    2 * (D * ((13 * A + 20) / ρ ^ 2) + A ^ 2 / ρ ^ 2) ≤
      (8 + 80000 * (13 * A + 20 + A ^ 2)) * T - (4 * f * r ^ 2 + 1) - 2 * r := by
  have e1 : (13 * A + 20) / ρ ^ 2 = (13 * A + 20) * (40000 * r ^ 4) := by rw [← hρ2]; ring
  have e2 : A ^ 2 / ρ ^ 2 = A ^ 2 * (40000 * r ^ 4) := by rw [← hρ2]; ring
  have i1 : D * r ^ 4 ≤ T := le_trans (mul_le_mul_of_nonneg_right hD (by positivity)) n6
  have i2 := mul_le_mul_of_nonneg_left i1 (show 0 ≤ 13 * A + 20 by positivity)
  have i3 := mul_le_mul_of_nonneg_left n7 (sq_nonneg A)
  rw [e1, e2]
  linarith

theorem quarter {a ρ : ℝ} (hρ : 0 < ρ) (ha : 0 ≤ a) (h : a ≤ ρ / 2) : a ^ 2 / ρ ^ 2 ≤ 1 / 4 := by
  rw [div_le_iff₀ (by positivity)]
  nlinarith

theorem contDiff_cut {n : ℕ} {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (ρ : ℝ) :
    ContDiff ℝ ∞ fun w : V n => χ (‖w‖ ^ 2 / ρ ^ 2) :=
  hχ.comp ((contDiff_norm_sq ℂ).div_const _)

theorem contDiff_eta {n : ℕ} {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (ρ : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ContDiff ℝ ∞ fun w : V n => χ (‖w‖ ^ 2 / ρ ^ 2) * Real.log ((‖w‖ ^ 2 / ρ ^ 2 + δ) / 2) :=
  (contDiff_cut hχ ρ).mul (((((contDiff_norm_sq ℂ).div_const _).add contDiff_const).div_const _).log
    fun w => by positivity)

def eta (n : ℕ) (χ : ℝ → ℝ) (ρ : ℝ) (k : ℕ) (w : V n) : ℝ :=
  n * (χ (‖w‖ ^ 2 / ρ ^ 2) * Real.log ((‖w‖ ^ 2 / ρ ^ 2 + 1 / ((k : ℝ) + 1)) / 2))

theorem delta_le (k : ℕ) : 1 / ((k : ℝ) + 1) ≤ 1 := by
  rw [div_le_one (by positivity)]
  linarith [Nat.cast_nonneg (α := ℝ) k]

theorem eta_zero {n : ℕ} {χ : ℝ → ℝ} (h0 : ∀ t, 1 ≤ t → χ t = 0) {ρ : ℝ} (hρ : 0 < ρ) (k : ℕ) {w : V n}
    (hw : ρ ≤ ‖w‖) : eta n χ ρ k w = 0 := by
  rw [eta, h0 _ (by rw [one_le_div (by positivity)]; gcongr), zero_mul, mul_zero]

theorem eta_nonpos {n : ℕ} {χ : ℝ → ℝ} (hr : ∀ t, 0 ≤ χ t ∧ χ t ≤ 1) (h0 : ∀ t, 1 ≤ t → χ t = 0) (ρ : ℝ)
    (k : ℕ) (w : V n) : eta n χ ρ k w ≤ 0 := by
  refine mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg n) ?_
  by_cases ht : 1 ≤ ‖w‖ ^ 2 / ρ ^ 2
  · rw [h0 _ ht, zero_mul]
  · refine mul_nonpos_of_nonneg_of_nonpos (hr _).1 (Real.log_nonpos (by positivity) ?_)
    linarith [delta_le k]

theorem eta_succ_le {n : ℕ} {χ : ℝ → ℝ} (hr : ∀ t, 0 ≤ χ t ∧ χ t ≤ 1) (ρ : ℝ)
    (k : ℕ) (w : V n) : eta n χ ρ (k + 1) w ≤ eta n χ ρ k w := by
  refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (Real.log_le_log (by positivity) ?_) (hr _).1)
    (Nat.cast_nonneg n)
  have : 1 / (((k + 1 : ℕ) : ℝ) + 1) ≤ 1 / ((k : ℝ) + 1) := by
    gcongr
    simp
  linarith

theorem eta_lower {n : ℕ} {χ : ℝ → ℝ} (hr : ∀ t, 0 ≤ χ t ∧ χ t ≤ 1) {ρ : ℝ} (hρ : 0 < ρ)
    (k : ℕ) {w : V n} (hw : ρ / 2 ≤ ‖w‖) : -(3 * n) ≤ eta n χ ρ k w := by
  have ht : 1 / 4 ≤ ‖w‖ ^ 2 / ρ ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  have hδ : 0 < 1 / ((k : ℝ) + 1) := by positivity
  have h8 : -3 ≤ Real.log ((‖w‖ ^ 2 / ρ ^ 2 + 1 / ((k : ℝ) + 1)) / 2) := by
    have h1 : Real.log (1 / 8) ≤ Real.log ((‖w‖ ^ 2 / ρ ^ 2 + 1 / ((k : ℝ) + 1)) / 2) :=
      Real.log_le_log (by norm_num) (by linarith)
    have h2 : Real.log (1 / 8) = -(3 * Real.log 2) := by
      rw [one_div, Real.log_inv, show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
    linarith [Real.log_two_lt_d9]
  have h3 : -3 ≤ χ (‖w‖ ^ 2 / ρ ^ 2) * Real.log ((‖w‖ ^ 2 / ρ ^ 2 + 1 / ((k : ℝ) + 1)) / 2) := by
    nlinarith [(hr (‖w‖ ^ 2 / ρ ^ 2)).1, (hr (‖w‖ ^ 2 / ρ ^ 2)).2]
  have := mul_le_mul_of_nonneg_left h3 (Nat.cast_nonneg (α := ℝ) n)
  rw [eta]
  linarith

theorem numerics {f r : ℝ} (hf : 1 ≤ f) (hr : 1 ≤ r) :
    1 ≤ (f * r) ^ 8 ∧ r ≤ (f * r) ^ 8 ∧ f * r ^ 2 * f ≤ (f * r) ^ 8 ∧ f * r ^ 2 ≤ (f * r) ^ 8 ∧
      f ≤ (f * r) ^ 8 ∧ f * r ^ 2 * r ^ 4 ≤ (f * r) ^ 8 ∧ r ^ 4 ≤ (f * r) ^ 8 := by
  have key : ∀ a b : ℕ, a ≤ 8 → b ≤ 8 → f ^ a * r ^ b ≤ (f * r) ^ 8 := fun a b ha hb => by
    rw [mul_pow]
    exact mul_le_mul (pow_le_pow_right₀ hf ha) (pow_le_pow_right₀ hr hb) (by positivity) (by positivity)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using key 0 0 (by norm_num) (by norm_num)
  · simpa using key 0 1 (by norm_num) (by norm_num)
  · exact le_of_eq_of_le (by ring) (key 2 2 (by norm_num) (by norm_num))
  · exact le_of_eq_of_le (by ring) (key 1 2 (by norm_num) (by norm_num))
  · simpa using key 1 0 (by norm_num) (by norm_num)
  · exact le_of_eq_of_le (by ring) (key 1 6 (by norm_num) (by norm_num))
  · simpa using key 0 4 (by norm_num) (by norm_num)

theorem peak_weight : ∃ C1 : ℝ, 0 ≤ C1 ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (la : ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r) (x : Frame X.Ψ r), 0 < X.p0 → X.p0 < r → ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x → (∀ τ (a b : Fin r), (b : ℕ) = a + 1 → (b : ℕ) ≠ X.p0 → C1 * ((X.Ψ.card : ℝ) * r) ^ 8 ≤ (la τ a : ℝ) - la τ b) → (∀ τ (a b : Fin r), (a : ℕ) = 0 → (b : ℕ) = r - 1 → C1 * ((X.Ψ.card : ℝ) * r) ^ 8 ≤ (la τ b : ℝ) - la τ a) → (∀ γ ∈ X.Γ, ∀ z z' : ReciprocityTheory.L2DbarEstimates.V (ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X), ‖z‖ ≤ 1 / (100 * (r : ℝ) ^ 2) → ‖z'‖ ≤ 1 / (100 * (r : ℝ) ^ 2) → ∀ b ∈ Bor X.Ψ r, lact γ (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z) = rmul (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z') b → γ = 1) → ∃ (ρ c : ℝ) (F0 : V (nd X) → ℂ) (ψ : ℕ → Frame X.Ψ r → ℝ) (φ : ℕ → V (nd X) → ℝ) (h : V (nd X) → ℝ≥0∞), 0 < ρ ∧ ρ ≤ 1 / (100 * (r : ℝ) ^ 2) ∧ 0 < c ∧ Metric.closedBall (0 : V (nd X)) ρ ⊆ OmF X x ∧ muF X x (Metric.ball 0 (1 / (100 * (r : ℝ) ^ 2)) ∩ OmF X x) < ⊤ ∧ ContDiffOn ℝ ∞ F0 (OmF X x) ∧ (∀ z, ‖z‖ ≤ ρ / 2 → F0 z = 1) ∧ (∀ z, ρ ≤ ‖z‖ → F0 z = 0) ∧ (∀ z, ‖F0 z‖ ≤ 1) ∧ (∀ k, Measurable (ψ k)) ∧ (∀ k, ∀ y ∈ X.dom, ∀ b ∈ Bor X.Ψ r, ψ k (rmul y b) = ψ k y) ∧ (∀ k, ∀ γ ∈ X.Γ, ∀ y ∈ X.dom, ψ k (lact γ y) = ψ k y) ∧ (∀ k y, ψ k y ≤ 0) ∧ (∀ k, ∀ z ∈ OmF X x, φ k z = phla X la (cpt X x z) - (4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 + 1) * rhF X x z - Real.log (densF X x z) + ψ k (cpt X x z)) ∧ (∀ k, ContDiffOn ℝ ∞ (φ k) (OmF X x)) ∧ (∀ k, ∀ z ∈ OmF X x, ∀ ξ : Fin (nd X) → ℂ, 0 ≤ (leviV (nd X) (fun w => ((φ k w : ℝ) : ℂ)) z ξ).re) ∧ (∀ k, ∀ z ∈ OmF X x, φ (k + 1) z ≤ φ k z) ∧ Measurable h ∧ (∀ k, ∀ z ∈ OmF X x, ∀ ξ : Fin (nd X) → ℂ, ENNReal.ofReal (‖∑ j, wdb (nd X) j F0 z * (starRingEnd ℂ) (ξ j)‖ ^ 2) ≤ h z * ENNReal.ofReal (leviV (nd X) (fun w => ((φ k w : ℝ) : ℂ)) z ξ).re) ∧ (∀ k, ∫⁻ z in OmF X x, h z * ENNReal.ofReal (Real.exp (-φ k z)) ≤ ENNReal.ofReal (Real.exp (C1 * ((∑ τ, ∑ a, |(la τ a : ℝ)|) + ((X.Ψ.card : ℝ) * r) ^ 8))) * muF X x (Metric.ball 0 ρ ∩ OmF X x)) ∧ (∀ z ∈ Metric.ball (0 : V (nd X)) ρ, Real.exp (-phla X la (cpt X x z)) * Real.exp ((4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 + 1) * rhF X x z) ≤ Real.exp (C1 * ((∑ τ, ∑ a, |(la τ a : ℝ)|) + ((X.Ψ.card : ℝ) * r) ^ 8))) ∧ (∀ w ∈ Metric.ball (0 : V (nd X)) (ρ / 2), ENNReal.ofReal (c * ‖w‖ ^ (-(2 * (nd X : ℝ)))) ≤ ⨆ k, ENNReal.ofReal (Real.exp (-ψ k (cpt X x w)))) ∧ (∀ w ∈ Metric.ball (0 : V (nd X)) (ρ / 2), ENNReal.ofReal (c * ‖w‖ ^ (-(2 * (nd X : ℝ)))) ≤ ⨆ k, ENNReal.ofReal (Real.exp (-φ k w))) := by
  obtain ⟨χ, A, hA, hχ, hχr, hχ1, hχ0, hd1, hd2⟩ := exists_cutoff
  refine ⟨8 + 80000 * (13 * A + 20 + A ^ 2), by positivity, ?_⟩
  intro E _ _ _ r X la x hp0 hp1 hx hg1 hg2 hinj
  set C1 : ℝ := 8 + 80000 * (13 * A + 20 + A ^ 2) with hC1
  have hC8 : 8 ≤ C1 := le_add_of_nonneg_right (by positivity)
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast (hp0.trans hp1)
  have hf1 := one_le_card X
  obtain ⟨n1, n2, n3, n4, n5, n6, n7⟩ := numerics hf1 hr1
  have hD := nd_le X
  set f : ℝ := (X.Ψ.card : ℝ) with hf
  set T : ℝ := (f * r) ^ 8 with hT
  set S : ℝ := ∑ τ, ∑ a, |(la τ a : ℝ)| with hS
  have hS0 : 0 ≤ S := by positivity
  set bb : ℝ := 4 * f * (r : ℝ) ^ 2 + 1 with hbb
  have hbb0 : 0 ≤ bb := by positivity
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ, ρ = 1 / (200 * (r : ℝ) ^ 2) := ⟨_, rfl⟩
  have hρ0 : 0 < ρ := by rw [hρ]; positivity
  have hρR : ρ < 1 / (100 * (r : ℝ) ^ 2) := by
    rw [hρ]
    exact one_div_lt_one_div_of_lt (by positivity) (by linarith [show (0 : ℝ) < (r : ℝ) ^ 2 by positivity])
  have hρ2 : 1 / ρ ^ 2 = 40000 * (r : ℝ) ^ 4 := by rw [hρ]; field_simp; norm_num
  have hsz := fun (z : V (nd X)) (hz : ‖z‖ ≤ 1 / (100 * (r : ℝ) ^ 2)) => GlobalTheory.T.chartBall_weightPotential_density_bounds E r X la x z hx hz
  have hdom : ∀ z : V (nd X), ‖z‖ ≤ 1 / (100 * (r : ℝ) ^ 2) → z ∈ OmF X x := fun z hz => (hsz z hz).1
  choose ψ ha hb hl hrm using fun k : ℕ => GlobalTheory.T.chartBall_extend_by_zero_invariant E r X x _ hx hdom hinj (eta (nd X) χ ρ k)
  have hcpt : ∀ k (z : V (nd X)), ‖z‖ ≤ 1 / (100 * (r : ℝ) ^ 2) → ψ k (cpt X x z) = eta (nd X) χ ρ k z := by
    intro k z hz
    have := ha k 1 X.Γ.one_mem _ (ExtFPf.oneF_mem X) z hz
    rwa [ExtFPf.rmul_oneF, KU.lact_one] at this
  have hb' : ∀ k y, (¬ ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, ∃ z : V (nd X), ‖z‖ ≤ ρ ∧
      y = lact γ (rmul (cpt X x z) b)) → ψ k y = 0 := by
    intro k y hy
    by_cases hc : ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, ∃ z : V (nd X), ‖z‖ ≤ 1 / (100 * (r : ℝ) ^ 2) ∧
      y = lact γ (rmul (cpt X x z) b)
    · obtain ⟨γ, hγ, b, hbB, z, hz, e⟩ := hc
      rw [e, ha k γ hγ b hbB z hz]
      refine eta_zero hχ0 hρ0 k (not_lt.1 fun h => hy ⟨γ, hγ, b, hbB, z, h.le, e⟩)
    · exact hb k y hc
  have hηs : ∀ k, ContDiff ℝ ∞ (eta (nd X) χ ρ k) := fun k =>
    contDiff_const.mul (contDiff_eta hχ ρ (by positivity))
  have hsm := fun k => GlobalTheory.T.invariantExtension_measurable_contDiffOn_chart E r X x ρ _ _ (ψ k) hx hρR hdom (hηs k) (ha k) (hb' k)
    (GlobalTheory.T.eventually_not_mem_chartBall_saturation E r X x ρ fun w hw => hdom w (hw.trans hρR.le))
  have hlevi := fun k : ℕ => levi_lower X hx hp0 hp1 la (g := C1 * T) (bb := bb)
    (K := nd X * ((13 * A + 20) / ρ ^ 2)) (M := A ^ 2 / ρ ^ 2) (ρ := ρ) (by positivity) hbb0
    (by positivity) (by positivity)
    (margin_num hA hρ2 hD n1 n2 n4 n6 n7)
    hρR hg1 hg2 (η := eta (nd X) χ ρ k) (ψ := ψ k)
    (fun z ξ => by
      have h := GlobalTheory.T.leviForm_cutoffLogWeight_lower_bound χ A hχ hχr hχ1 hχ0 hd1 hd2 (nd X) ρ (1 / ((k : ℝ) + 1)) hρ0 (by positivity)
        (delta_le k) z ξ
      have h2 : ContDiffAt ℝ 2 (fun w : V (nd X) => χ (‖w‖ ^ 2 / ρ ^ 2) *
          Real.log ((‖w‖ ^ 2 / ρ ^ 2 + 1 / ((k : ℝ) + 1)) / 2)) z :=
        (contDiff_eta hχ ρ (by positivity)).contDiffAt.of_le HE.two_le_inf
      unfold eta
      rw [Y.LocalMaximumSecondDerivative.leviV_ofReal_const_mul _ h2, Complex.re_ofReal_mul]
      have := mul_le_mul_of_nonneg_left h (Nat.cast_nonneg (α := ℝ) (nd X))
      linarith)
    (ha k) (hb' k) (hl k) (hrm k) (hsm k).2
  have hψcase : ∀ y, (∃ z, ∀ k, ψ k y = eta (nd X) χ ρ k z) ∨ ∀ k, ψ k y = 0 := by
    intro y
    by_cases hc : ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, ∃ z : V (nd X), ‖z‖ ≤ 1 / (100 * (r : ℝ) ^ 2) ∧
      y = lact γ (rmul (cpt X x z) b)
    · obtain ⟨γ, hγ, b, hbB, z, hz, e⟩ := hc
      exact Or.inl ⟨z, fun k => by rw [e, ha k γ hγ b hbB z hz]⟩
    · exact Or.inr fun k => hb k y hc
  have hbf : bb * f ≤ 5 * T := by rw [hbb]; linarith
  have hrh : ∀ z : V (nd X), ‖z‖ ≤ 1 / (100 * (r : ℝ) ^ 2) → |bb * rhF X x z| ≤ bb * f := fun z hz => by
    rw [abs_mul, abs_of_nonneg hbb0]
    exact mul_le_mul_of_nonneg_left (hsz z hz).2.2.1 hbb0
  have hST : S + 8 * T ≤ C1 * (S + T) := by
    have := mul_le_mul_of_nonneg_right hC8 (show 0 ≤ S + T by linarith)
    linarith
  have hhalf : ∀ k (w : V (nd X)), ‖w‖ < ρ / 2 → ψ k (cpt X x w) =
      nd X * Real.log ((‖w‖ ^ 2 / ρ ^ 2 + 1 / ((k : ℝ) + 1)) / 2) := by
    intro k w hw
    rw [hcpt k w (by linarith), eta, hχ1 _ (quarter hρ0 (norm_nonneg w) hw.le), one_mul]
  set c0 : ℝ := Real.exp (-(S + bb * f + f * r)) with hc0
  refine ⟨ρ, c0 * ρ ^ (2 * nd X), fun w => ((χ (‖w‖ ^ 2 / ρ ^ 2) : ℝ) : ℂ), ψ,
    fun k w => phla X la (cpt X x w) - bb * rhF X x w - Real.log (densF X x w) + ψ k (cpt X x w),
    {w : V (nd X) | ρ / 2 ≤ ‖w‖ ∧ ‖w‖ < ρ}.indicator (fun _ => (1 : ℝ≥0∞)), hρ0, hρR.le, by positivity,
    fun z hz => hdom z ((mem_closedBall_zero_iff.1 hz).trans hρR.le), muF_ball_lt_top X hx,
    (Complex.ofRealCLM.contDiff.comp (contDiff_cut hχ ρ)).contDiffOn, fun z hz => ?_, fun z hz => ?_,
    fun z => ?_, fun k => (hsm k).1, fun k y _ b hbB => hrm k y b hbB, fun k γ hγ y _ => hl k γ hγ y,
    fun k y => ?_, fun k z _ => rfl, fun k => weight_smooth X hx la bb (hsm k).2, fun k z hz ξ => ?_,
    fun k z hz => ?_, ?_, fun k z hz ξ => ?_, fun k => ?_, fun z hz => ?_, fun w hw => ?_, fun w hw => ?_⟩
  · simp only
    rw [hχ1 _ (quarter hρ0 (norm_nonneg z) hz), Complex.ofReal_one]
  · simp only
    rw [hχ0 _ (by rw [one_le_div (by positivity)]; gcongr), Complex.ofReal_zero]
  · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hχr _).1]
    exact (hχr _).2
  · rcases hψcase y with ⟨z, h⟩ | h
    · rw [h]; exact eta_nonpos hχr hχ0 ρ k z
    · rw [h]
  · rw [weight_levi X hx la bb (hsm k).2 hz]
    exact (hlevi k).2 z hz ξ
  · have : ψ (k + 1) (cpt X x z) ≤ ψ k (cpt X x z) := by
      rcases hψcase (cpt X x z) with ⟨z', h⟩ | h
      · rw [h, h]; exact eta_succ_le hχr ρ k z'
      · rw [h, h]
    simp only
    linarith
  · refine measurable_const.indicator ?_
    exact (measurableSet_le measurable_const measurable_norm).inter
      (measurableSet_lt measurable_norm measurable_const)
  · have h := GlobalTheory.T.dbarDeriv_cutoff_normSq_bound_annulus χ A hχ hχr hχ1 hχ0 hd1 (nd X) ρ hρ0 z ξ
    by_cases hz' : ρ / 2 ≤ ‖z‖ ∧ ‖z‖ < ρ
    · rw [if_pos hz'] at h
      rw [Set.indicator_of_mem (by exact hz'), one_mul, weight_levi X hx la bb (hsm k).2 hz]
      exact ENNReal.ofReal_le_ofReal (h.trans ((hlevi k).1 z (hz'.2.trans hρR) ξ))
    · rw [if_neg hz'] at h
      rw [ENNReal.ofReal_eq_zero.2 h]
      exact zero_le
  · refine annulus_integral X x (Real.exp_pos _).le fun z h1 h2 => ?_
    have hz := (h2.trans hρR).le
    obtain ⟨-, s1, -, -, s4⟩ := hsz z hz
    have s5 := eta_lower hχr hρ0 k h1
    conv_rhs => rw [← Real.exp_log s4, ← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    beta_reduce
    rw [hcpt k z hz]
    linarith [(abs_le.1 s1).1, (abs_le.1 (hrh z hz)).2]
  · have hz' := ((mem_ball_zero_iff.1 hz).trans hρR).le
    rw [← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    linarith [(abs_le.1 (hsz z hz').2.1).1, (abs_le.1 (hrh z hz')).2]
  · refine pole hρ0 (Real.exp_pos _).le w _ fun k => ?_
    rw [hhalf k w (mem_ball_zero_iff.1 hw)]
    refine mul_le_of_le_one_left (Real.exp_pos _).le (Real.exp_le_one_iff.2 ?_)
    have : 0 ≤ S + bb * f + f * r := by positivity
    linarith
  · refine pole hρ0 (Real.exp_pos _).le w _ fun k => ?_
    have hw' : ‖w‖ < ρ / 2 := mem_ball_zero_iff.1 hw
    have hw2 : ‖w‖ ≤ 1 / (100 * (r : ℝ) ^ 2) := by linarith
    simp only
    rw [hhalf k w hw', ← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    linarith [(abs_le.1 (hsz w hw2).2.1).2, (abs_le.1 (hrh w hw2)).1, (abs_le.1 (hsz w hw2).2.2.2.1).1]

end

end GlobalTheory.PeakWeight
