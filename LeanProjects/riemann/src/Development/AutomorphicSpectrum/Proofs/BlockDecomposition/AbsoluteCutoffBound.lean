import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.FriedrichsKernels.Friedrichs

noncomputable section

open Filter Topology
open scoped ZeroAtInfty InnerProductSpace ComplexConjugate

namespace GlobalTheory.CompanionTheory.FcCut

open PositivityTheory.RgBcC.Fc

def mulC (a : ℝ → ℂ) (ha : Continuous a) (f : C₀(ℝ, ℂ)) (R : ℝ) (hf : ∀ y, R ≤ |y| → a y * f y = 0) :
    C₀(ℝ, ℂ) :=
  ⟨⟨fun y => a y * f y, ha.mul f.continuous⟩, by
    have hK : (Set.Icc (-R) R)ᶜ ∈ cocompact ℝ := isCompact_Icc.compl_mem_cocompact
    refine (tendsto_const_nhds (x := (0 : ℂ))).congr' ?_
    filter_upwards [hK] with y hy
    have hR : R ≤ |y| := by
      by_contra hlt
      push_neg at hlt
      exact hy ⟨(abs_lt.mp hlt).1.le, (abs_lt.mp hlt).2.le⟩
    show (0 : ℂ) = a y * f y
    rw [hf y hR]⟩

@[simp] theorem mulC_apply (a : ℝ → ℂ) (ha : Continuous a) (f : C₀(ℝ, ℂ)) (R : ℝ)
    (hf : ∀ y, R ≤ |y| → a y * f y = 0) (y : ℝ) : mulC a ha f R hf y = a y * f y := rfl

section Core

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : Submodule ℂ H} {Ω : M →ₗ[ℂ] M} {T : H →L[ℂ] H}

theorem inner_star_mul (F : FCalc H M Ω T) (x : H) (a b : C₀(ℝ, ℂ)) :
    ⟪F.Φ (star a * b) x, x⟫_ℂ = ⟪F.Φ b x, F.Φ a x⟫_ℂ := by
  rw [F.map_mul, F.map_star, ContinuousLinearMap.mul_apply,
    ContinuousLinearMap.adjoint_inner_left]

theorem core (F : FCalc H M Ω T) (c : ℝ) (x : H)
    (hyp : ∀ g, ∃ v : M, (v : H) = F.Φ g x ∧ (⟪(Ω v : H), v⟫_ℂ).re ≤ c * ‖(v : H)‖ ^ 2)
    (f : C₀(ℝ, ℂ)) (δ R : ℝ) (hδ : 0 < δ) (h1 : ∀ y, y ≤ c + δ → f y = 0)
    (h2 : ∀ y, R ≤ |y| → f y = 0) : F.Φ f x = 0 := by
  let h := mulC (fun y => (y : ℂ)) Complex.continuous_ofReal f R
    (fun y hy => by rw [h2 y hy, mul_zero])
  let r := mulC (fun y => ((Real.sqrt (max (y - c - δ) 0) : ℝ) : ℂ))
    (Complex.continuous_ofReal.comp (by fun_prop)) f R (fun y hy => by rw [h2 y hy, mul_zero])
  obtain ⟨v, hv, hle⟩ := hyp f
  have hΩ : (Ω v : H) = F.Φ h x := F.omega f h (fun y => rfl) x v hv
  have hid : star r * r = star f * h - ((c + δ : ℝ) : ℂ) • (star f * f) := by
    ext y
    by_cases hy : y ≤ c + δ
    · simp [r, h, h1 y hy]
    · have hpos : 0 ≤ y - c - δ := by linarith [not_le.mp hy]
      have hs : ((Real.sqrt (y - c - δ) : ℝ) : ℂ) * ((Real.sqrt (y - c - δ) : ℝ) : ℂ)
          = (y : ℂ) - c - δ := by
        rw [← Complex.ofReal_mul, Real.mul_self_sqrt hpos]; push_cast; ring
      simp only [r, h, ZeroAtInftyContinuousMap.coe_mul, ZeroAtInftyContinuousMap.coe_star,
        ZeroAtInftyContinuousMap.coe_sub, ZeroAtInftyContinuousMap.coe_smul, Pi.mul_apply, Pi.star_apply,
        Pi.sub_apply, Pi.smul_apply, mulC_apply, max_eq_left hpos, star_mul', smul_eq_mul]
      simp only [Complex.star_def, Complex.conj_ofReal]
      push_cast
      linear_combination ((starRingEnd ℂ) (f y) * f y) * hs
  have e : ((‖F.Φ r x‖ ^ 2 : ℝ) : ℂ) = ⟪(Ω v : H), v⟫_ℂ - ((c + δ : ℝ) : ℂ) * ((‖(v : H)‖ ^ 2 : ℝ) : ℂ) := by
    have a1 := inner_star_mul F x r r
    have a2 := inner_star_mul F x f h
    have a3 := inner_star_mul F x f f
    rw [hid, map_sub, map_smul, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      inner_sub_left, inner_smul_left, a2, a3, Complex.conj_ofReal,
      inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at a1
    rw [hΩ, hv]
    push_cast
    simpa using a1.symm
  have e' := congrArg Complex.re e
  rw [Complex.ofReal_re, Complex.sub_re, Complex.re_ofReal_mul, Complex.ofReal_re] at e'
  have hn : ‖(v : H)‖ ^ 2 ≤ 0 := by
    have p1 : 0 ≤ ‖F.Φ r x‖ ^ 2 := by positivity
    nlinarith
  have hv0 : ‖(v : H)‖ = 0 := by
    have := sq_nonneg ‖(v : H)‖
    exact pow_eq_zero_iff (two_ne_zero) |>.mp (le_antisymm hn this)
  rw [← hv]
  exact norm_eq_zero.mp hv0

theorem approx (c : ℝ) (g : C₀(ℝ, ℂ)) (hg : ∀ y, y ≤ c → g y = 0) (ε : ℝ) (hε : 0 < ε) :
    ∃ (f : C₀(ℝ, ℂ)) (δ R : ℝ), 0 < δ ∧ (∀ y, y ≤ c + δ → f y = 0) ∧ (∀ y, R ≤ |y| → f y = 0) ∧
      ‖g - f‖ ≤ 2 * ε := by

  obtain ⟨R, hR⟩ : ∃ R : ℝ, ∀ y, R ≤ |y| → ‖g y‖ ≤ ε := by
    have ht : Tendsto g (cocompact ℝ) (𝓝 0) := g.zero_at_infty'
    have hm : {y | ‖g y‖ < ε} ∈ cocompact ℝ := by
      have := ht (Metric.ball_mem_nhds (0 : ℂ) hε)
      simpa [Metric.ball, dist_zero_right] using this
    obtain ⟨t, ht1, ht2⟩ := Filter.mem_cocompact.mp hm
    obtain ⟨r, hr⟩ := ht1.isBounded.subset_closedBall (0 : ℝ)
    refine ⟨r + 1, fun y hy => ?_⟩
    have hyt : y ∈ tᶜ := fun hyt => by
      have := hr hyt
      rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at this
      linarith
    exact (ht2 hyt).le

  obtain ⟨δ, hδ, hδc⟩ : ∃ δ > 0, ∀ y, y ≤ c + δ → ‖g y‖ ≤ ε := by
    obtain ⟨d, hd, hdc⟩ := Metric.continuous_iff.mp g.continuous c ε hε
    refine ⟨d / 2, by positivity, fun y hy => ?_⟩
    by_cases hyc : y ≤ c
    · rw [hg y hyc, norm_zero]; exact hε.le
    · have : dist y c < d := by
        rw [Real.dist_eq, abs_of_pos (by linarith [not_le.mp hyc])]
        linarith
      have h3 : dist (g y) (g c) < ε := hdc y this
      rw [hg c le_rfl, dist_zero_right] at h3
      exact h3.le
  let m : ℝ → ℝ := fun y => min 1 (max 0 (‖g y‖ / ε - 1))
  have hm0 : ∀ y, ‖g y‖ ≤ ε → m y = 0 := fun y hy => by
    have : ‖g y‖ / ε - 1 ≤ 0 := by
      rw [sub_nonpos, div_le_one hε]; exact hy
    simp only [m, max_eq_left this]
    exact min_eq_right zero_le_one
  have hmc : Continuous m := by
    have := g.continuous
    fun_prop
  let f := mulC (fun y => (m y : ℂ)) (Complex.continuous_ofReal.comp hmc) g R
    (fun y hy => by rw [hm0 y (hR y hy)]; simp)
  refine ⟨f, δ, R, hδ, fun y hy => ?_, fun y hy => ?_, ?_⟩
  · simp [f, hm0 y (hδc y hy)]
  · simp [f, hm0 y (hR y hy)]
  · rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
    refine (BoundedContinuousFunction.norm_le (by positivity)).mpr fun y => ?_
    have hy : (g - f).toBCF y = (1 - (m y : ℂ)) * g y := by
      show g y - (m y : ℂ) * g y = _
      ring
    rw [hy, norm_mul]
    have hm1 : m y ≤ 1 := min_le_left _ _
    have hm2 : 0 ≤ m y := le_min zero_le_one (le_max_left _ _)
    have hn : ‖(1 - (m y : ℂ))‖ = 1 - m y := by
      have : (1 - (m y : ℂ)) = ((1 - m y : ℝ) : ℂ) := by push_cast; ring
      rw [this, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
    rw [hn]
    by_cases hb : 2 * ε ≤ ‖g y‖
    · have : m y = 1 := by
        have h1 : 1 ≤ ‖g y‖ / ε - 1 := by
          have : 2 ≤ ‖g y‖ / ε := by rw [le_div_iff₀ hε]; exact hb
          linarith
        exact min_eq_left (h1.trans (le_max_right _ _))
      rw [this]; simp; positivity
    · have hgy := (not_le.mp hb).le
      have : 0 ≤ ‖g y‖ := norm_nonneg _
      nlinarith

theorem absCut : AbsCut := by
  intro H _ _ _ M Ω T F c x hyp g hg
  refine norm_eq_zero.mp (le_antisymm (le_of_forall_pos_le_add fun e he => ?_) (norm_nonneg _))
  have hx : 0 < ‖x‖ + 1 := by positivity
  obtain ⟨f, δ, R, hδ, h1, h2, hfg⟩ := approx c g hg (e / (2 * (‖x‖ + 1))) (by positivity)
  have hz := core F c x hyp f δ R hδ h1 h2
  have hsplit : F.Φ g x = F.Φ (g - f) x := by
    rw [map_sub, ContinuousLinearMap.sub_apply, hz, sub_zero]
  have hb : ‖F.Φ (g - f) x‖ ≤ 2 * (e / (2 * (‖x‖ + 1))) * ‖x‖ :=
    ((F.Φ (g - f)).le_opNorm x).trans
      (mul_le_mul_of_nonneg_right ((F.norm_le _).trans hfg) (norm_nonneg _))
  have hc : 2 * (e / (2 * (‖x‖ + 1))) * ‖x‖ ≤ e := by
    have : 2 * (e / (2 * (‖x‖ + 1))) * ‖x‖ = e * (‖x‖ / (‖x‖ + 1)) := by
      field_simp
    rw [this]
    have : ‖x‖ / (‖x‖ + 1) ≤ 1 := by
      rw [div_le_one hx]; linarith
    nlinarith
  rw [hsplit]
  linarith

end Core

end GlobalTheory.CompanionTheory.FcCut
