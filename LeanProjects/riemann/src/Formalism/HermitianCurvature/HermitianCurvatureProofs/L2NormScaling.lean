import Formalism.HermitianCurvature.HermitianCurvatureProofs.UhMeasurableSet

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal ComplexConjugate

noncomputable section

set_option maxHeartbeats 1600000

namespace Formalism.FourierDecayAlt.P.DDSmoothness

open Formalism.FourierDecayAlt.ThreeDimData

section Alg

variable {k r : ℕ} {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]

theorem inner_self_cast (a : Wp) : ⟪a, a⟫_ℂ = ((‖a‖ ^ 2 : ℝ) : ℂ) := by
  apply Complex.ext
  · rw [Complex.ofReal_re]
    exact inner_self_eq_norm_sq (𝕜 := ℂ) a
  · rw [Complex.ofReal_im]
    exact inner_self_im (𝕜 := ℂ) a

theorem l2_norm_scaling {νq : Measure (Formalism.QuantumDeterminants.Mt k r)} (T F : Mx k r → Wp) (a : Wp) (U D : ℝ) (hU : 0 ≤ U)
    (hN : PI.BesselPeriodGGP.l2SG (k := k) (r := r) νq T =
      ENNReal.ofReal (U * (⟪a, ⟪a, a⟫_ℂ • a⟫_ℂ).re / D))
    (hae : ∀ᵐ x ∂νq, T (Matrix.of x) = ⟪a, a⟫_ℂ • F (Matrix.of x)) :
    ENNReal.ofReal (‖a‖ ^ 2) * PI.BesselPeriodGGP.l2SG (k := k) (r := r) νq F =
      ENNReal.ofReal (U * ‖a‖ ^ 2 / D) := by
  have hinner : ⟪a, a⟫_ℂ = ((‖a‖ ^ 2 : ℝ) : ℂ) := inner_self_cast a
  have hnq : ‖⟪a, a⟫_ℂ‖ = ‖a‖ ^ 2 := by
    rw [hinner, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hc : (‖⟪a, a⟫_ℂ‖₊ : ENNReal) = ENNReal.ofReal (‖a‖ ^ 2) := by
    rw [← hnq]
    exact (ENNReal.ofReal_eq_coe_nnreal (norm_nonneg _)).symm
  have hT : PI.BesselPeriodGGP.l2SG (k := k) (r := r) νq T =
      ENNReal.ofReal (‖a‖ ^ 2) ^ 2 * PI.BesselPeriodGGP.l2SG (k := k) (r := r) νq F := by
    unfold PI.BesselPeriodGGP.l2SG
    rw [← lintegral_const_mul' (ENNReal.ofReal (‖a‖ ^ 2) ^ 2) _ (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)]
    refine lintegral_congr_ae (hae.mono fun x hx => ?_)
    dsimp only
    rw [hx, nnnorm_smul, ENNReal.coe_mul, mul_pow, hc]
  have hre : (⟪a, ⟪a, a⟫_ℂ • a⟫_ℂ).re = ‖a‖ ^ 4 := by
    rw [inner_smul_right, hinner, ← Complex.ofReal_mul, Complex.ofReal_re]
    ring
  rw [hT, hre] at hN
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  have hp : 0 < ‖a‖ ^ 2 := pow_pos (norm_pos_iff.mpr ha) 2
  have key : ENNReal.ofReal (‖a‖ ^ 2) * (ENNReal.ofReal (‖a‖ ^ 2) * PI.BesselPeriodGGP.l2SG (k := k) (r := r) νq F) =
      ENNReal.ofReal (‖a‖ ^ 2) * ENNReal.ofReal (U * ‖a‖ ^ 2 / D) := by
    rw [← mul_assoc, ← pow_two, hN, ← ENNReal.ofReal_mul hp.le]
    congr 1
    ring
  exact (ENNReal.mul_right_inj (ENNReal.ofReal_pos.mpr hp).ne' ENNReal.ofReal_ne_top).mp key

end Alg

theorem shape_of (hPsi : PsiConst) (hSch : SchurH) (hBC : BeConv) (hNI : NormIdSm) (hBB : BeBessel) : Shape := by
  intro hIn k r ε lam h H _ _ _ σ w0 Wp _ _ _ _ z c u π μW μN μG νq hS hnz
  have hS' := hS
  obtain ⟨hlam, hσ, -, -, hw0, hz, hT, hc, hπ, -, -, -, -⟩ := hS'
  have hsm := DD_smooth hIn.2.2.1 hlam hσ hw0
  obtain ⟨-, -, -, hBC4⟩ := hBC hIn k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS
  obtain ⟨x0, hx0, y0, hy0, hne⟩ := hnz
  obtain ⟨ξ0, hξ0⟩ : ∃ ξ, be z c π σ μW μN x0 y0 ξ ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hne (ContinuousLinearMap.ext hcon)
  have hB0 := hBB hIn k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS y0 (Or.inl hy0) ξ0
  set B0 : H → Wp := fun x => be z c π σ μW μN x y0 ξ0 with hB0def
  have hB0x : B0 x0 ≠ 0 := hξ0
  have hcoef : ∀ v ∈ DDsp σ w0, ∀ ξ : Wp, ∃ κ : ℂ, ∀ x ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ,
      be z c π σ μW μN x v ξ = κ • B0 x := fun v hv ξ =>
    jsz_line hIn.2.2.2 hPsi hlam hσ hz hT hc hπ hB0
      (hBB hIn k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS v (Or.inl hv) ξ) (hsm x0 hx0) hB0x
  choose! cf hcf using hcoef
  have herm : ∀ x ∈ DDsp σ w0, ∀ v ∈ DDsp σ w0, ∀ η ξ : Wp,
      cf v ξ * ⟪η, B0 x⟫_ℂ = conj (cf x η) * ⟪B0 v, ξ⟫_ℂ := by
    intro x hx v hv η ξ
    have hadj := (hBC4 x hx v (Or.inl hv)).2
    have e := ContinuousLinearMap.adjoint_inner_left (be z c π σ μW μN x v) ξ η
    rw [hadj, hcf v hv ξ x (hsm x hx), hcf x hx η v (hsm v hv), inner_smul_left, inner_smul_right] at e
    exact e.symm
  have hη : ⟪B0 x0, B0 x0⟫_ℂ ≠ 0 := inner_self_ne_zero.mpr hB0x
  set κ : ℂ := conj (cf x0 (B0 x0)) / ⟪B0 x0, B0 x0⟫_ℂ with hκdef
  have hcf' : ∀ v ∈ DDsp σ w0, ∀ ξ, cf v ξ = κ * ⟪B0 v, ξ⟫_ℂ := by
    intro v hv ξ
    have e := herm x0 hx0 v hv (B0 x0) ξ
    rw [hκdef, div_mul_eq_mul_div, eq_div_iff hη]
    linear_combination e
  have hform : ∀ x ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ, ∀ v ∈ DDsp σ w0, ∀ ξ,
      be z c π σ μW μN x v ξ = (κ * ⟪B0 v, ξ⟫_ℂ) • B0 x := fun x hx v hv ξ => by
    rw [hcf v hv ξ x hx, hcf' v hv ξ]
  have hκ0 : κ ≠ 0 := by
    intro h0
    apply hξ0
    show be z c π σ μW μN x0 y0 ξ0 = 0
    rw [hform x0 (hsm x0 hx0) y0 hy0 ξ0, h0, zero_mul, zero_smul]
  have hpos := (hNI hIn hSch k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS x0 (hsm x0 hx0) x0 (Or.inl hx0)
    (B0 x0)).2
  rw [hform x0 (hsm x0 hx0) x0 hx0, inner_smul_right, inner_self_cast] at hpos
  set N2 : ℝ := ‖B0 x0‖ ^ 2 with hN2
  have hN2pos : 0 < N2 := by rw [hN2]; have := norm_pos_iff.mpr hB0x; positivity
  have hexp : κ * (N2 : ℂ) * (N2 : ℂ) = κ * ((N2 * N2 : ℝ) : ℂ) := by push_cast; ring
  rw [hexp, Complex.mul_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im] at hpos
  simp only [mul_zero, zero_add, sub_zero] at hpos
  have hNN : 0 < N2 * N2 := mul_pos hN2pos hN2pos
  have him : κ.im = 0 := by
    rcases mul_eq_zero.mp hpos.1 with h1 | h1
    · exact h1
    · exact absurd h1 hNN.ne'
  have hre0 : 0 ≤ κ.re := by
    by_contra hneg; push_neg at hneg
    have : κ.re * (N2 * N2) < 0 := mul_neg_of_neg_of_pos hneg hNN
    linarith [hpos.2]
  have hre : 0 < κ.re := by
    rcases hre0.lt_or_eq with h1 | h1
    · exact h1
    · exact absurd (Complex.ext (by simp [← h1]) (by simp [him])) hκ0
  set s : ℝ := Real.sqrt κ.re with hs
  have hss : (s : ℂ) * (s : ℂ) = κ := by
    rw [← Complex.ofReal_mul, hs, Real.mul_self_sqrt hre.le]
    exact Complex.ext (by simp) (by simp [him])
  have hspos : 0 < s := Real.sqrt_pos.mpr hre
  refine ⟨fun x => (s : ℂ) • B0 x, bessel_smul hB0 _, ⟨x0, hx0, ?_⟩, ?_⟩
  · exact smul_ne_zero (by exact_mod_cast hspos.ne') hB0x
  · intro x hx v hv
    ext ξ
    simp only [ContinuousLinearMap.smulRight_apply, innerSL_apply_apply]
    rw [hform x hx v hv ξ, inner_smul_left, Complex.conj_ofReal, smul_smul]
    congr 1
    rw [← hss]; ring

theorem kFinForm_of (hPsi : PsiConst) (hBC : BeConv) (hBB : BeBessel) : KFinForm := by
  intro hIn k r ε lam h H _ _ _ σ w0 Wp _ _ _ _ z c u π μW μN μG νq hS l hl hx1e hid v hv x hx
  obtain ⟨x1, hx1, hlx1⟩ := hx1e
  have hS' := hS
  obtain ⟨hlam, hσ, -, -, hw0, hz, hT, hc, hπ, -, -, -, -⟩ := hS'
  have hsm := DD_smooth hIn.2.2.1 hlam hσ hw0
  have hvs : v ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ := hIn.2.2.1 k r ε lam H σ hlam hσ v hv
  obtain ⟨-, -, -, hBC4⟩ := hBC hIn k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS
  ext ξ
  obtain ⟨κ, hκ⟩ := jsz_line hIn.2.2.2 hPsi hlam hσ hz hT hc hπ hl
    (hBB hIn k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS v (Or.inr hv) ξ) (hsm x1 hx1) hlx1
  have hadj := (hBC4 x1 hx1 v (Or.inr hv)).2
  have e := ContinuousLinearMap.adjoint_inner_left (be z c π σ μW μN x1 v) ξ (l x1)
  rw [hadj, hκ x1 (hsm x1 hx1), hid v hvs x1 hx1] at e
  simp only [ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, inner_smul_left, inner_smul_right,
    inner_conj_symm] at e
  have hn : ⟪l x1, l x1⟫_ℂ ≠ 0 := inner_self_ne_zero.mpr hlx1
  have hκv : κ = ⟪l v, ξ⟫_ℂ := by
    apply mul_left_cancel₀ hn
    linear_combination -e
  rw [hκ x hx, hκv]
  simp only [ContinuousLinearMap.smulRight_apply, innerSL_apply_apply]

theorem discrete_form_one_side : DDFormOneOfSteps := by
  intro hPsi hSch _ _ _ _ hBC hNI hBB hSh hIn k r ε lam h H _ _ _ σ w0 Wp _ _ _ _ z c u π μW μN μG νq hS
  have hS' := hS
  obtain ⟨hlam, hσ, -, -, hw0, -, -, -, -, hW, hN, hG, hq⟩ := hS'
  have hsm := DD_smooth hIn.2.2.1 hlam hσ hw0
  obtain ⟨hBC1, -, -, -⟩ := hBC hIn k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS
  obtain ⟨d, hd, hSd⟩ := hSch k r ε lam H σ μG hlam hσ hG
  have hw0n : w0 ≠ 0 := by
    obtain ⟨P, -, hn1, -⟩ := hw0
    intro h0; rw [h0, norm_zero] at hn1; exact zero_ne_one hn1
  have hdeg : ∀ x : H, x ≠ 0 → PI.BesselPeriodGGP.fdegH μG σ x = d := fun x hx => fdeg_eq hd hSd hx
  have hmu := muSof_facts hW hN
  have hae := ae_UH_of_quot hG.2.2.1 hmu.1 hmu.2 hq
  by_cases hnz : ∃ x ∈ DDsp σ w0, ∃ y ∈ DDsp σ w0, be z c π σ μW μN x y ≠ 0
  · obtain ⟨l, hl, -, hid⟩ := hSh hIn k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS hnz
    refine ⟨l, hl, fun x hx v hv => ⟨hBC1 x (hsm x hx) v (Or.inl hv), hid x (hsm x hx) v hv⟩, ?_⟩
    intro x hx hx0 v hv
    have hNv := (hNI hIn hSch k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS x (hsm x hx) v (Or.inl hv) (l v)).1
    rw [hid v (hsm v hv) v hv] at hNv
    simp only [ContinuousLinearMap.smulRight_apply, innerSL_apply_apply] at hNv
    rw [hdeg w0 hw0n] at hNv
    rw [hdeg x hx0]
    refine l2_norm_scaling _ _ (l v) _ _ (by positivity) hNv (hae.mono fun g hg => ?_)
    rw [hid _ (PI.UnitaryGroupMassFormula.CapelliEig.smooth_right_action k r ε lam H σ hσ x (hsm x hx) _ hg) v hv]
    simp only [ContinuousLinearMap.smulRight_apply, innerSL_apply_apply]
  · push_neg at hnz
    refine ⟨fun _ => 0, bessel_zero, fun x hx v hv => ⟨hBC1 x (hsm x hx) v (Or.inl hv), ?_⟩,
      fun x _ _ v _ => by simp⟩
    show be z c π σ μW μN x v = _
    rw [hnz x hx v hv]
    ext ξ; simp

end Formalism.FourierDecayAlt.P.DDSmoothness
