import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyRayDataOfNeZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LatticeThetaAsymptoticsStatement
open Complex Filter Asymptotics

namespace GlobalTheory

open Set MeasureTheory
open scoped Topology

theorem summable_shiftedLattice_normSq_rpow (w₁ w₂ x₀ : ℂ)
    (h : (starRingEnd ℂ w₁ * w₂).im ≠ 0) {σ : ℝ} (hσ : 1 < σ) :
    Summable fun p : ℤ × ℤ => (‖x₀ + p.1 * w₁ + p.2 * w₂‖ ^ 2 : ℝ) ^ (-σ) := by
  have hli : ∀ a b : ℝ, a • w₁ + b • w₂ = 0 → a = 0 ∧ b = 0 := by
    intro a b hab
    have h1 := congrArg Complex.re hab
    have h2 := congrArg Complex.im hab
    simp at h1 h2 h
    have h' : w₁.re * w₂.im - w₁.im * w₂.re ≠ 0 := by
      intro h0; apply h; linarith
    constructor
    · apply mul_right_cancel₀ h'
      linear_combination w₂.im * h1 - w₂.re * h2
    · apply mul_right_cancel₀ h'
      linear_combination w₁.re * h2 - w₁.im * h1
  let L : PeriodPair := ⟨w₁, w₂, LinearIndependent.pair_iff.mpr hli⟩
  have hs := ZLattice.summable_norm_sub_rpow L.lattice (-(2 * σ)) (by simp; linarith) (-x₀)
  let φ : ℤ × ℤ → L.lattice := fun p =>
    ⟨p.1 * w₁ + p.2 * w₂, PeriodPair.mem_lattice.mpr ⟨p.1, p.2, rfl⟩⟩
  have hφ : Function.Injective φ := by
    intro p q hpq
    have e : (p.1 * w₁ + p.2 * w₂ : ℂ) = q.1 * w₁ + q.2 * w₂ := congrArg Subtype.val hpq
    have := hli (p.1 - q.1) (p.2 - q.2) (by simp; linear_combination e)
    simp only [sub_eq_zero, Int.cast_inj] at this
    exact Prod.ext this.1 this.2
  refine (hs.comp_injective hφ).congr fun p => ?_
  simp only [Function.comp, φ]
  rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
  congr 1
  · congr 1; ring
  · push_cast; ring

theorem summable_exp_neg_pi_mul_of_summable_rpow {ι : Type*} {q : ι → ℝ} (hq : ∀ i, 0 < q i)
    (hs : Summable fun i => q i ^ (-(2 : ℝ))) {t : ℝ} (ht : 0 < t) :
    Summable fun i => Real.exp (-Real.pi * t * q i) := by
  refine Summable.of_nonneg_of_le (fun i => (Real.exp_pos _).le) (fun i => ?_)
    (hs.mul_left (2 / (Real.pi * t) ^ 2))
  have hx : 0 < Real.pi * t * q i := by have := hq i; positivity
  have h1 := Real.pow_div_factorial_le_exp _ hx.le 2
  have h2 : -Real.pi * t * q i = -(Real.pi * t * q i) := by ring
  have h3 : (2 / (Real.pi * t) ^ 2) * q i ^ (-(2 : ℝ))
      = ((Real.pi * t * q i) ^ 2 / (Nat.factorial 2 : ℕ))⁻¹ := by
    have := hq i
    rw [Real.rpow_neg (hq i).le, Real.rpow_two]
    simp only [Nat.factorial_two, Nat.cast_ofNat]
    field_simp
  rw [h2, h3, Real.exp_neg]
  exact inv_anti₀ (by positivity) h1

theorem continuousOn_tsum_exp_neg_pi_mul {ι : Type*} {q : ι → ℝ} (hq : ∀ i, 0 < q i)
    (hs : Summable fun i => q i ^ (-(2 : ℝ))) :
    ContinuousOn (fun t : ℝ => ∑' i, Real.exp (-Real.pi * t * q i)) (Ioi 0) := by
  intro t ht
  have ht' : 0 < t / 2 := half_pos ht
  have : ContinuousOn (fun t : ℝ => ∑' i, Real.exp (-Real.pi * t * q i)) (Ioi (t / 2)) := by
    refine continuousOn_tsum (fun i => by fun_prop)
      (summable_exp_neg_pi_mul_of_summable_rpow hq hs ht') fun i x hx => ?_
    rw [Real.norm_eq_abs, Real.abs_exp]
    apply Real.exp_le_exp.mpr
    have h1 : t / 2 < x := hx
    have := mul_pos (mul_pos Real.pi_pos (sub_pos.mpr h1)) (hq i)
    linarith
  exact (this.continuousAt (Ioi_mem_nhds (half_lt_self ht))).continuousWithinAt

theorem isBigO_exp_neg_div_rpow {c : ℝ} (hc : 0 < c) (b : ℝ) :
    (fun t : ℝ => Real.exp (-c / t)) =O[𝓝[>] 0] (fun t : ℝ => t ^ (-b)) := by
  refine ((isLittleO_exp_neg_mul_rpow_atTop hc b).isBigO.comp_tendsto
    tendsto_inv_nhdsGT_zero).congr' (.of_forall fun t => ?_)
    (eventually_mem_nhdsWithin.mono fun t ht => ?_)
  · simp [div_eq_mul_inv]
  · simp only [Function.comp]
    rw [Real.inv_rpow (le_of_lt ht), Real.rpow_neg (le_of_lt ht)]

theorem exists_entire_dirichlet_of_theta {ι : Type*} [Countable ι] {q : ι → ℝ}
    (hq : ∀ i, 0 < q i) (hs : ∀ σ : ℝ, 1 < σ → Summable fun i => q i ^ (-σ)) {V c : ℝ}
    (hc : 0 < c)
    (htop : (fun t : ℝ => ∑' i, Real.exp (-Real.pi * t * q i)) =O[atTop]
      (fun t => Real.exp (-c * t)))
    (hbot : (fun t : ℝ => (∑' i, Real.exp (-Real.pi * t * q i)) - 1 / (t * V)) =O[𝓝[>] 0]
      (fun t => Real.exp (-c / t))) :
    ∃ Z : ℂ → ℂ, Differentiable ℂ Z ∧ Z 1 = (Real.pi / V : ℝ) ∧ Z (-1) = 0 ∧
      ∀ s : ℂ, 1 < s.re → Summable (fun i => ((q i : ℝ) : ℂ) ^ (-s)) ∧
        Z s = (s - 1) * ∑' i, ((q i : ℝ) : ℂ) ^ (-s) := by
  set θ : ℝ → ℝ := fun t => ∑' i, Real.exp (-Real.pi * t * q i) with hθ
  have hθc : ContinuousOn θ (Ioi 0) := continuousOn_tsum_exp_neg_pi_mul hq (hs 2 one_lt_two)
  let g : ℝ → ℂ := indicator (Ioc 0 1) (fun t => (t : ℂ) ^ (-1 : ℂ))
  let A : ℂ := (V : ℂ)⁻¹
  let f : ℝ → ℂ := fun t => (θ t : ℂ) - A • g t
  have hfc : LocallyIntegrableOn f (Ioi 0) := by
    refine LocallyIntegrableOn.sub
      ((continuous_ofReal.comp_continuousOn hθc).locallyIntegrableOn measurableSet_Ioi)
      (LocallyIntegrableOn.smul ?_ A)
    have h0 : LocallyIntegrableOn (fun t : ℝ => (t : ℂ) ^ (-1 : ℂ)) (Ioi 0) :=
      ContinuousOn.locallyIntegrableOn (continuousOn_of_forall_continuousAt fun t ht =>
        continuousAt_ofReal_cpow_const _ _ (Or.inr <| ne_of_gt ht)) measurableSet_Ioi
    intro x hx
    obtain ⟨u, hu, hu'⟩ := h0 x hx
    exact ⟨u, hu, hu'.indicator measurableSet_Ioc⟩
  have hftop : f =O[atTop] fun t => Real.exp (-c * t) := by
    refine (isBigO_ofReal_left.mpr htop).congr' ?_ EventuallyEq.rfl
    filter_upwards [eventually_gt_atTop 1] with t ht
    simp [f, g, indicator_of_notMem (fun h : t ∈ Ioc (0:ℝ) 1 => h.2.not_gt ht)]
  have hfbot : ∀ b : ℝ, f =O[𝓝[>] 0] fun t => t ^ (-b) := by
    intro b
    refine ((isBigO_ofReal_left.mpr hbot).congr' ?_ EventuallyEq.rfl).trans
      (isBigO_exp_neg_div_rpow hc b)
    filter_upwards [Ioc_mem_nhdsGT (zero_lt_one' ℝ)] with t ht
    simp only [f, g, A, indicator_of_mem ht, cpow_neg_one, smul_eq_mul, θ]
    push_cast
    ring
  have hdiff : Differentiable ℂ (mellin f) := fun s =>
    mellin_differentiableAt_of_isBigO_rpow_exp hc hfc hftop (hfbot (s.re - 1)) (sub_one_lt _)
  have hpi : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  refine ⟨fun s => (Real.pi : ℂ) ^ s * (Gamma s)⁻¹ * ((s - 1) * mellin f s + A), ?_, ?_, ?_, ?_⟩
  · refine (Differentiable.mul (differentiable_id.const_cpow (Or.inl hpi))
      differentiable_one_div_Gamma).mul ?_
    exact ((differentiable_id.sub_const 1).mul hdiff).add_const A
  · simp [A, div_eq_mul_inv]
  · have : Gamma (-1) = 0 := by simpa using Gamma_neg_nat_eq_zero 1
    simp [this]
  · intro s hs1
    have hs0 : 0 < s.re := by linarith
    have hsum : HasSum (fun i => (Real.pi : ℂ) ^ (-s) * Gamma s * (1 : ℂ) / (q i : ℂ) ^ s)
        (mellin (fun t => (θ t : ℂ)) s) := by
      refine hasSum_mellin_pi_mul (a := fun _ => 1) (fun i => Or.inr (hq i)) hs0
        (fun t ht => ?_) ?_
      · have := (summable_exp_neg_pi_mul_of_summable_rpow hq (hs 2 one_lt_two) ht).hasSum
        rw [← hasSum_ofReal] at this
        convert this using 3 with i
        rw [one_mul]; congr 2; ring
      · refine (hs s.re hs1).congr fun i => ?_
        rw [Real.rpow_neg (hq i).le, norm_one, one_div]
    have hg := hasMellin_cpow_Ioc (-1) (s := s) (by simp; linarith)
    have hgA := hasMellin_const_smul hg.1 A
    have hfm : MellinConvergent f s :=
      mellinConvergent_of_isBigO_rpow_exp hc hfc hftop (hfbot 0) hs0
    have hadd := (hasMellin_add hfm hgA.1).2
    have e1 : (fun t => f t + A • g t) = fun t => (θ t : ℂ) := by
      funext t; simp [f]
    rw [hgA.2, hg.2] at hadd
    have hadd' : mellin (fun t => (θ t : ℂ)) s = mellin f s + A • (1 / (s + -1)) := by
      rw [← e1]; exact hadd
    have hG : Gamma s ≠ 0 := Gamma_ne_zero_of_re_pos hs0
    have hp : (Real.pi : ℂ) ^ s ≠ 0 := by simp [cpow_eq_zero_iff]
    have hs1' : s - 1 ≠ 0 := by
      intro h0; rw [sub_eq_zero.mp h0] at hs1; simp at hs1
    have hsum2 : HasSum (fun i => ((q i : ℝ) : ℂ) ^ (-s))
        ((Real.pi : ℂ) ^ s * (Gamma s)⁻¹ * mellin (fun t => (θ t : ℂ)) s) := by
      refine HasSum.congr_fun (hsum.mul_left ((Real.pi : ℂ) ^ s * (Gamma s)⁻¹)) fun i => ?_
      rw [cpow_neg, cpow_neg]
      field_simp
    refine ⟨hsum2.summable, ?_⟩
    rw [hsum2.tsum_eq, hadd', ← sub_eq_add_neg, smul_eq_mul]
    field_simp

theorem epsteinZeta_shifted_continuation : ∀ (w₁ w₂ x₀ : ℂ), (starRingEnd ℂ w₁ * w₂).im ≠ 0 → (∀ m n : ℤ, x₀ + m * w₁ + n * w₂ ≠ 0) → ∃ Z : ℂ → ℂ, Differentiable ℂ Z ∧ Z 1 = (Real.pi / |(starRingEnd ℂ w₁ * w₂).im| : ℝ) ∧ Z (-1) = 0 ∧ ∀ s : ℂ, 1 < s.re → Summable (fun p : ℤ × ℤ => ((‖x₀ + p.1 * w₁ + p.2 * w₂‖ ^ 2 : ℝ) : ℂ) ^ (-s)) ∧ Z s = (s - 1) * ∑' p : ℤ × ℤ, ((‖x₀ + p.1 * w₁ + p.2 * w₂‖ ^ 2 : ℝ) : ℂ) ^ (-s) := by
  intro w₁ w₂ x₀ h hx
  obtain ⟨c, hc, htop, hbot⟩ := GlobalTheory.T.lattice_theta_asymptotics w₁ w₂ x₀ h hx
  exact exists_entire_dirichlet_of_theta
    (q := fun p : ℤ × ℤ => ‖x₀ + p.1 * w₁ + p.2 * w₂‖ ^ 2)
    (fun p => pow_pos (norm_pos_iff.mpr (hx p.1 p.2)) 2)
    (fun σ hσ => summable_shiftedLattice_normSq_rpow w₁ w₂ x₀ h hσ) hc htop hbot

end GlobalTheory
