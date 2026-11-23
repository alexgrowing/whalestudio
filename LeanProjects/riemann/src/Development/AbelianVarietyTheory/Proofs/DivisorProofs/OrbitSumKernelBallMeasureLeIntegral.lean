import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.KronHolPsiStatementHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.PoinStatementPfI
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitSumExpPotentialUniformBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoinConvBdd
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MeasurableSetSatFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetNearOneMatrixNormBoundsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramChartSubFormEntryLeStatement
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory
open scoped ENNReal

namespace GlobalTheory.BallSum

open ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem norm_lminor_Gw_ge (X : Data E r) (w : V (nd X)) (τ : X.Ψ) (hw : 3 * (r : ℝ) * ‖w‖ ≤ 1 / 2) :
    (1 / 2 : ℝ) ^ r ≤ ‖lminor (Gw X w τ) (i0 X)‖ := by
  have hw0 : (r : ℝ) * ‖w‖ ≤ 1 := by nlinarith [norm_nonneg w]
  have hp : X.p0 ≤ r := X.p0_le
  have key := (GlobalTheory.T.det_near_one_matrix_norm_bounds X.p0 ((Gw X w τ).submatrix (Fin.castLE X.p0_le) (Fin.castLE X.p0_le))
    (3 * ‖w‖) (fun i j => ?_) ?_).1
  · unfold lminor
    refine le_trans ?_ key
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hp
  · have hJ : Jd X (Fin.castLE X.p0_le i) (Fin.castLE X.p0_le j) = (1 : Matrix (Fin X.p0) (Fin X.p0) ℂ) i j := by
      simp only [Jd, Matrix.diagonal_apply, Matrix.one_apply, Fin.castLE_inj]
      split_ifs with h
      · subst h; simp [sgn, i.isLt]
      · rfl
    rw [Matrix.submatrix_apply, ← hJ]
    exact GlobalTheory.T.gramChart_sub_form_entry_le E r X w τ _ _ hw0
  · have : (X.p0 : ℝ) ≤ r := by exact_mod_cast hp
    nlinarith [norm_nonneg w]

theorem rhY_cpt_le (X : Data E r) {x0 x : Frame X.Ψ r} (hx0 : IsOrth X x0) (hx : IsOrth X x)
    (hr : 0 < r) (w : V (nd X)) (hw : ‖w‖ ≤ 1 / (100 * (r : ℝ) ^ 2)) :
    rhY X x0 (cpt X x w) ≤ rhY X x0 x + X.Ψ.card * (3 * r * Real.log 2) := by
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hrw : 100 * (r : ℝ) ^ 2 * ‖w‖ ≤ 1 := by
    rw [le_div_iff₀ (by positivity)] at hw; linarith
  have hp : (X.p0 : ℝ) ≤ r := by exact_mod_cast X.p0_le
  have hw3 : 3 * (r : ℝ) * ‖w‖ ≤ 1 / 2 := by nlinarith [norm_nonneg w]
  have hterm : ∀ τ : X.Ψ, -(Real.log ‖dmin X.Gm (cpt X x w) τ (i0 X)‖ -
      2 * Real.log ‖lminor (gM X x0 (cpt X x w) τ) (i0 X)‖) ≤
        -(Real.log ‖dmin X.Gm x τ (i0 X)‖ - 2 * Real.log ‖lminor (gM X x0 x τ) (i0 X)‖) +
          3 * r * Real.log 2 := by
    intro τ
    have hd1 : ‖dmin X.Gm x τ (i0 X)‖ = 1 := norm_dmin_orth' X hx τ _
    have hA : -Real.log ‖dmin X.Gm (cpt X x w) τ (i0 X)‖ ≤ r * Real.log 2 := by
      rw [dmin_cpt_orth X hx]
      have h1 := norm_lminor_Gw_ge X w τ hw3
      have h2 : Real.log ((1 / 2 : ℝ) ^ r) ≤ Real.log ‖lminor (Gw X w τ) (i0 X)‖ :=
        Real.log_le_log (by positivity) h1
      rw [Real.log_pow, one_div, Real.log_inv] at h2
      linarith
    have hM22 := (sumBd_weight (Mq_isUpq X hx0 hx τ)).1
    have hnorm : ∀ y, ‖lminor (gM X x0 y τ) (i0 X)‖ = ‖(Mq X x0 y τ).toBlocks₂₂.det‖ := fun y => by
      rw [det_lowerBlock_eq_conj_minor, Complex.norm_conj]; rfl
    have hPP := GlobalTheory.T.det_near_one_matrix_norm_bounds X.p0 (((Mq X x0 x τ).toBlocks₂₂)⁻¹ * (Mq X x0 x τ).toBlocks₂₁ *
        (Nw X w τ).toBlocks₁₂ + (Nw X w τ).toBlocks₂₂) (((r : ℝ) + 1) * ‖w‖)
        (fun i j => pert_entry X hx0 hx w τ i j) (by nlinarith [norm_nonneg w])
    have hP := hPP.2
    have h0 : 0 < ‖(((Mq X x0 x τ).toBlocks₂₂)⁻¹ * (Mq X x0 x τ).toBlocks₂₁ *
        (Nw X w τ).toBlocks₁₂ + (Nw X w τ).toBlocks₂₂).det‖ := lt_of_lt_of_le (by positivity) hPP.1
    have hpos : 0 < ‖(Mq X x0 x τ).toBlocks₂₂.det‖ := norm_pos_iff.2 hM22
    have hB : Real.log ‖lminor (gM X x0 (cpt X x w) τ) (i0 X)‖ ≤
        Real.log ‖lminor (gM X x0 x τ) (i0 X)‖ + r * Real.log 2 := by
      rw [hnorm, hnorm, Mq_cpt', det_split _ _ hM22, norm_mul]
      rw [Real.log_mul hpos.ne' h0.ne']
      have h2 : Real.log ‖(((Mq X x0 x τ).toBlocks₂₂)⁻¹ * (Mq X x0 x τ).toBlocks₂₁ *
          (Nw X w τ).toBlocks₁₂ + (Nw X w τ).toBlocks₂₂).det‖ ≤ X.p0 * Real.log 2 := by
        rw [← Real.log_pow]; exact Real.log_le_log h0 hP
      have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
      nlinarith
    rw [hd1, Real.log_one]
    linarith
  unfold rhY
  rw [← Finset.sum_neg_distrib, ← Finset.sum_neg_distrib]
  calc ∑ τ, -(Real.log ‖dmin X.Gm (cpt X x w) τ (i0 X)‖ - 2 * Real.log ‖lminor (gM X x0 (cpt X x w) τ) (i0 X)‖)
      ≤ ∑ τ : X.Ψ, (-(Real.log ‖dmin X.Gm x τ (i0 X)‖ - 2 * Real.log ‖lminor (gM X x0 x τ) (i0 X)‖) +
          3 * r * Real.log 2) := Finset.sum_le_sum fun τ _ => hterm τ
    _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]

end GlobalTheory.BallSum

namespace GlobalTheory.BallSum

open ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem lintegral_orbit_le (X : Data E r) {x y : Frame X.Ψ r} (hx : IsOrth X x) (hy : IsOrth X y)
    {A : Set (V (nd X))} (hA : MeasurableSet A) (hAO : A ⊆ OmF X x) {φ : Frame X.Ψ r → ℝ≥0∞}
    (hφ : Measurable φ) (hφB : ∀ u ∈ X.dom, ∀ b ∈ Bor X.Ψ r, φ (rmul u b) = φ u)
    (hinj : ∀ γ ∈ X.Γ, ∀ z ∈ A, ∀ z' ∈ A, ∀ b ∈ Bor X.Ψ r,
      lact γ (cpt X x z) = rmul (cpt X x z') b → γ = 1) :
    ∫⁻ z in A, ∑' γ : X.Γ, φ (lact γ.1 (cpt X x z)) ∂muF X x ≤ ∫⁻ z, φ (cpt X y z) ∂muF X y := by
  classical
  have := FundSetPf.countable_GL (E := E) (r := r)
  have hS := GlobalTheory.Unfold.measurableSet_satFrames X hx hA hAO
  have hc : Measurable (cpt X x) := (FundSetPf.cont_cpt X x).measurable
  let χ : X.Γ → Frame X.Ψ r → ℝ≥0∞ := fun γ =>
    ((fun u => lact (γ.1)⁻¹ u) ⁻¹' GlobalTheory.Unfold.satFrames X x A).indicator φ
  have hχm : ∀ γ, Measurable (χ γ) := fun γ =>
    hφ.indicator ((GlobalTheory.Unfold.continuous_lact X _).measurable hS)
  have hχB : ∀ γ, ∀ u ∈ X.dom, ∀ b ∈ Bor X.Ψ r, χ γ (rmul u b) = χ γ u := by
    intro γ u hu b hb
    simp only [χ, Set.indicator, Set.mem_preimage, FundSetPf.lact_rmul,
      GlobalTheory.Unfold.rmul_mem_satFrames_iff X x A _ hb, hφB u hu b hb]
  have hterm : ∀ γ : X.Γ, ∫⁻ z in A, φ (lact γ.1 (cpt X x z)) ∂muF X x =
      ∫⁻ z, χ γ (cpt X x z) ∂muF X x := by
    intro γ
    rw [measInv_holds r X x (lact γ.1 x) hx (GlobalTheory.Unfold.isOrth_lact X hx γ.2) (χ γ) (hχm γ) (hχB γ),
      GlobalTheory.Unfold.muF_lact X x γ.2, ← lintegral_indicator hA]
    refine lintegral_congr fun z => ?_
    simp only [χ, Set.indicator, Set.mem_preimage, GlobalTheory.Unfold.cpt_lact, FundSetPf.lact_inv,
      GlobalTheory.Unfold.cpt_mem_satFrames_iff X hx]
  have huniq : ∀ (u : Frame X.Ψ r) (γ γ' : X.Γ), lact (γ.1)⁻¹ u ∈ GlobalTheory.Unfold.satFrames X x A →
      lact (γ'.1)⁻¹ u ∈ GlobalTheory.Unfold.satFrames X x A → γ = γ' := by
    intro u γ γ' hm hm'
    obtain ⟨z, hz, b, hb, h⟩ := hm
    obtain ⟨z', hz', b', hb', h'⟩ := hm'
    have hδ : (γ'.1)⁻¹ * γ.1 ∈ X.Γ := X.Γ.mul_mem (X.Γ.inv_mem γ'.2) γ.2
    have e1 : lact ((γ'.1)⁻¹ * γ.1) (rmul (cpt X x z) b) = rmul (cpt X x z') b' := by
      rw [← h, ← h', ← FundSetPf.lact_mul, mul_assoc, mul_inv_cancel, mul_one]
    have e2 : lact ((γ'.1)⁻¹ * γ.1) (cpt X x z) = rmul (cpt X x z') (rmul b' (ExtFPf.invF X b)) := by
      rw [← ExtFPf.rmul_assoc, ← e1, ← FundSetPf.lact_rmul, ExtFPf.rmul_assoc, ExtFPf.rmul_invF X hb,
        ExtFPf.rmul_oneF]
    have h1 := hinj _ hδ z hz z' hz' _ (ExtFPf.mul_mem X hb' (ExtFPf.invF_mem X hb)) e2
    exact Subtype.ext (inv_mul_eq_one.mp h1).symm
  have hpt : ∀ u, ∑' γ : X.Γ, χ γ u ≤ φ u := by
    intro u
    by_cases hT : ∃ γ : X.Γ, lact (γ.1)⁻¹ u ∈ GlobalTheory.Unfold.satFrames X x A
    · obtain ⟨γ0, hγ0⟩ := hT
      rw [tsum_eq_single γ0]
      · exact Set.indicator_le_self _ _ u
      · intro γ hne
        exact Set.indicator_of_notMem (s := (fun u => lact (γ.1)⁻¹ u) ⁻¹' GlobalTheory.Unfold.satFrames X x A)
          (fun hm => hne (huniq u γ γ0 hm hγ0)) φ
    · push_neg at hT
      have h0 : ∀ γ : X.Γ, χ γ u = 0 := fun γ =>
        Set.indicator_of_notMem (s := (fun u => lact (γ.1)⁻¹ u) ⁻¹' GlobalTheory.Unfold.satFrames X x A) (hT γ) φ
      simp [h0]
  calc ∫⁻ z in A, ∑' γ : X.Γ, φ (lact γ.1 (cpt X x z)) ∂muF X x
      = ∑' γ : X.Γ, ∫⁻ z in A, φ (lact γ.1 (cpt X x z)) ∂muF X x :=
        lintegral_tsum fun γ => ((hφ.comp (GlobalTheory.Unfold.continuous_lact X γ.1).measurable).comp hc).aemeasurable
    _ = ∑' γ : X.Γ, ∫⁻ z, χ γ (cpt X x z) ∂muF X x := tsum_congr hterm
    _ = ∫⁻ z, ∑' γ : X.Γ, χ γ (cpt X x z) ∂muF X x :=
        (lintegral_tsum fun γ => ((hχm γ).comp hc).aemeasurable).symm
    _ ≤ ∫⁻ z, φ (cpt X x z) ∂muF X x := lintegral_mono fun z => hpt _
    _ = ∫⁻ z, φ (cpt X y z) ∂muF X y := measInv_holds r X x y hx hy φ hφ hφB

end GlobalTheory.BallSum

namespace GlobalTheory.BallSum

open ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf

theorem const_le (f r : ℕ) : (4 * (f : ℝ) * (r : ℝ) ^ 2 + 1) * ((f : ℝ) * (3 * (r : ℝ) * Real.log 2)) ≤
    15 * ((f : ℝ) * r) ^ 8 := by
  have hl : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num); linarith
  have hl0 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  rcases Nat.eq_zero_or_pos f with hf | hf
  · subst hf; simp
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr; simp
  have hf1 : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  set a : ℝ := (f : ℝ) * r with ha
  have ha1 : 1 ≤ a := by nlinarith
  have h3 : a ^ 3 ≤ a ^ 8 := pow_le_pow_right₀ ha1 (by norm_num)
  have h1 : a ≤ a ^ 8 := by
    calc a = a ^ 1 := (pow_one a).symm
      _ ≤ a ^ 8 := pow_le_pow_right₀ ha1 (by norm_num)
  have hfr : (f : ℝ) ^ 2 * (r : ℝ) ^ 3 ≤ a ^ 3 := by
    rw [ha, mul_pow]
    have : (f : ℝ) ^ 2 ≤ (f : ℝ) ^ 3 := pow_le_pow_right₀ hf1 (by norm_num)
    exact mul_le_mul_of_nonneg_right this (by positivity)
  have hx : (4 * (f : ℝ) * (r : ℝ) ^ 2 + 1) * ((f : ℝ) * (3 * (r : ℝ) * Real.log 2)) ≤
      (4 * (f : ℝ) * (r : ℝ) ^ 2 + 1) * ((f : ℝ) * (3 * (r : ℝ))) := by
    have h := mul_le_mul_of_nonneg_left hl (show 0 ≤ 3 * (r : ℝ) by positivity)
    refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (by positivity)) (by positivity)
    linarith
  have he : (4 * (f : ℝ) * (r : ℝ) ^ 2 + 1) * ((f : ℝ) * (3 * (r : ℝ))) =
      12 * ((f : ℝ) ^ 2 * (r : ℝ) ^ 3) + 3 * a := by rw [ha]; ring
  linarith

theorem ballSum_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (x y : ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r), 0 < X.p0 → X.p0 < r → ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x → ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X y → (∀ γ ∈ X.Γ, ∀ z z' : ReciprocityTheory.L2DbarEstimates.V (ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X), ‖z‖ ≤ 1 / (100 * (r : ℝ) ^ 2) → ‖z'‖ ≤ 1 / (100 * (r : ℝ) ^ 2) → ∀ b ∈ Bor X.Ψ r, lact γ (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z) = rmul (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z') b → γ = 1) → ReciprocityTheory.ChartRestriction.G.AR.Up.muF X x (Metric.ball (0 : ReciprocityTheory.L2DbarEstimates.V (ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X)) (1 / (100 * (r : ℝ) ^ 2)) ∩ ReciprocityTheory.ChartRestriction.G.AR.Up.OmF X x) * ∑' γ : X.Γ, ENNReal.ofReal (ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf.kaY X x (4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 + 1) (lact γ.1 y)) ≤ ENNReal.ofReal (Real.exp (C * ((X.Ψ.card : ℝ) * r) ^ 8)) * ∫⁻ z, ENNReal.ofReal (ReciprocityTheory.ChartRestriction.G.AR.Up.kaF X y (4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 + 1) z) ∂(ReciprocityTheory.ChartRestriction.G.AR.Up.muF X y) := by
  refine ⟨15, by norm_num, ?_⟩
  intro E _ _ _ r X x y hp0 hp0r hx hy hinj
  classical
  haveI := FundSetPf.countable_GL (E := E) (r := r)
  have hr : 0 < r := by omega
  set s : ℝ := 4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 + 1 with hs
  have hs0 : 0 ≤ s := by positivity
  set ρ : ℝ := 1 / (100 * (r : ℝ) ^ 2) with hρ
  set A : Set (V (nd X)) := Metric.ball (0 : V (nd X)) ρ ∩ OmF X x with hAdef
  set K : ℝ := (X.Ψ.card : ℝ) * (3 * r * Real.log 2) with hK
  set k : ℝ≥0∞ := ENNReal.ofReal (Real.exp (s * K)) with hk
  set φ : Frame X.Ψ r → ℝ≥0∞ := fun u => ENNReal.ofReal (kaY X y s u) with hφdef
  have hφm : Measurable φ := ENNReal.measurable_ofReal.comp (meas_kaY X y s)
  have hφB : ∀ u ∈ X.dom, ∀ b ∈ Bor X.Ψ r, φ (rmul u b) = φ u := fun u hu b hb => by
    simp only [hφdef, kaY_rmul X hy hu hb]
  set G : Frame X.Ψ r → ℝ≥0∞ := fun u => ∑' δ : X.Γ, φ (lact δ.1 u) with hGdef

  have hsym : ∑' γ : X.Γ, ENNReal.ofReal (kaY X x s (lact γ.1 y)) = G x := by
    simp only [hGdef]
    rw [← (Equiv.inv X.Γ).tsum_eq (fun δ : X.Γ => φ (lact δ.1 x))]
    refine tsum_congr fun γ => ?_
    have hγi : (γ.1)⁻¹ ∈ X.Γ := X.Γ.inv_mem γ.2
    show ENNReal.ofReal (kaY X x s (lact γ.1 y)) = ENNReal.ofReal (kaY X y s (lact (γ.1)⁻¹ x))
    rw [GlobalTheory.PoinSumBound.kaY_eq_exp X hx (orth_mem_dom X (GlobalTheory.Unfold.isOrth_lact X hy γ.2)),
      GlobalTheory.PoinSumBound.kaY_eq_exp X hy (orth_mem_dom X (GlobalTheory.Unfold.isOrth_lact X hx hγi)),
      GlobalTheory.Up.rhX_lact (X.Γ_stab _ γ.2), GlobalTheory.OrbitSum.rhX_symm X (GlobalTheory.Unfold.isOrth_lact X hx hγi) hy]

  have hHar : ∀ w ∈ A, G x ≤ k * G (cpt X x w) := by
    intro w hw
    simp only [hGdef]
    rw [← ENNReal.tsum_mul_left]
    refine ENNReal.tsum_le_tsum fun δ => ?_
    have ho := GlobalTheory.Unfold.isOrth_lact X hx δ.2
    have hwn : ‖w‖ ≤ ρ := (mem_ball_zero_iff.1 hw.1).le
    have h := GlobalTheory.BallSum.rhY_cpt_le X hy ho hr w hwn
    show ENNReal.ofReal (kaY X y s (lact δ.1 x)) ≤ k * ENNReal.ofReal (kaY X y s (lact δ.1 (cpt X x w)))
    rw [← GlobalTheory.Unfold.cpt_lact, hk, ← ENNReal.ofReal_mul (Real.exp_pos _).le]
    refine ENNReal.ofReal_le_ofReal ?_
    unfold kaY
    rw [← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have := mul_le_mul_of_nonneg_left h hs0
    linarith

  have hAm : MeasurableSet A := measurableSet_ball.inter (OntoB.isOpen_OmF X x).measurableSet
  have h1 : muF X x A * G x ≤ k * ∫⁻ z in A, G (cpt X x z) ∂muF X x := by
    rw [mul_comm, ← setLIntegral_const, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact setLIntegral_mono' hAm fun z hz => hHar z hz

  have h2 : ∫⁻ z in A, G (cpt X x z) ∂muF X x ≤ ∫⁻ z, φ (cpt X y z) ∂muF X y :=
    lintegral_orbit_le X hx hy hAm Set.inter_subset_right hφm hφB
      fun γ hγ z hz z' hz' b hb e => hinj γ hγ z z' (mem_ball_zero_iff.1 hz.1).le
        (mem_ball_zero_iff.1 hz'.1).le b hb e
  have h3 : ∫⁻ z, φ (cpt X y z) ∂muF X y = ∫⁻ z, ENNReal.ofReal (kaF X y s z) ∂muF X y := by
    simp only [hφdef, kaY_cpt X hy]
  have hkC : k ≤ ENNReal.ofReal (Real.exp (15 * ((X.Ψ.card : ℝ) * r) ^ 8)) :=
    ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (const_le X.Ψ.card r))
  rw [hsym]
  calc muF X x A * G x ≤ k * ∫⁻ z in A, G (cpt X x z) ∂muF X x := h1
    _ ≤ k * ∫⁻ z, ENNReal.ofReal (kaF X y s z) ∂muF X y := mul_le_mul_of_nonneg_left (h2.trans h3.le) zero_le
    _ ≤ _ := mul_le_mul_of_nonneg_right hkC zero_le

end GlobalTheory.BallSum
