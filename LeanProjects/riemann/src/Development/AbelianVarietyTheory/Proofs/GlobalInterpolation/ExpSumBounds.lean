import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LamIdealOfNotPrimePow
open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical

namespace GlobalTheory.Hk

lemma integral_mul_exp_neg_Ioi {t : ℝ} (ht : 0 < t) (y : ℝ) :
    IntegrableOn (fun x : ℝ => t * Real.exp (-(t * x))) (Set.Ioi y) ∧
    ∫ x in Set.Ioi y, t * Real.exp (-(t * x)) = Real.exp (-(t * y)) := by
  have h1 := exp_neg_integrableOn_Ioi y ht
  have h2 := integral_exp_mul_Ioi (a := -t) (by linarith) y
  simp only [neg_mul] at h1 h2
  refine ⟨h1.const_mul t, ?_⟩
  rw [integral_const_mul, h2]
  field_simp

lemma tsum_exp_eq_integral (c : ℕ → ℂ) (h0 : c 0 = 0) {t : ℝ} (ht : 0 < t)
    (hs : Summable (fun n : ℕ => ‖c n‖ * Real.exp (-(t * n)))) :
    ∑' n : ℕ, c n * (Real.exp (-(t * n)) : ℂ) =
      ∫ x in Set.Ioi (1 : ℝ), (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, c n) * ((t * Real.exp (-(t * x)) : ℝ) : ℂ) := by
  set φ : ℕ → ℝ → ℝ := fun n x => (Set.Ici (n : ℝ)).indicator (fun x => t * Real.exp (-(t * x))) x with hφ
  have hφi : ∀ n, Integrable (φ n) (volume.restrict (Set.Ioi (1 : ℝ))) := fun n =>
    (integral_mul_exp_neg_Ioi ht 1).1.indicator measurableSet_Ici
  have hφ0 : ∀ n x, 0 ≤ φ n x := fun n x =>
    Set.indicator_nonneg (fun y _ => by positivity) x
  have hφv : ∀ n : ℕ, n ≠ 0 → ∫ x in Set.Ioi (1 : ℝ), φ n x = Real.exp (-(t * n)) := by
    intro n hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hn
    rw [hφ]
    simp only
    rw [setIntegral_indicator measurableSet_Ici, ← (integral_mul_exp_neg_Ioi ht n).2]
    apply setIntegral_congr_set
    have e1 : (Set.Ioi (1 : ℝ) : Set ℝ) =ᵐ[volume] Set.Ici 1 := Ioi_ae_eq_Ici
    have e2 : (Set.Ioi (1 : ℝ) ∩ Set.Ici (n : ℝ) : Set ℝ) =ᵐ[volume] (Set.Ici 1 ∩ Set.Ici (n : ℝ) : Set ℝ) :=
      ae_eq_set_inter e1 (ae_eq_refl _)
    rw [Set.Ici_inter_Ici, sup_eq_right.2 hn1] at e2
    exact e2.trans Ioi_ae_eq_Ici.symm
  have hv : ∀ n : ℕ, ∫ x in Set.Ioi (1 : ℝ), c n * (φ n x : ℂ) = c n * (Real.exp (-(t * n)) : ℂ) := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp [h0]
    · rw [integral_const_mul, integral_complex_ofReal, hφv n hn]
  have hn : ∀ n : ℕ, ∫ x in Set.Ioi (1 : ℝ), ‖c n * (φ n x : ℂ)‖ = ‖c n‖ * Real.exp (-(t * n)) := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp [h0]
    · simp only [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hφ0 _ _)]
      rw [integral_const_mul, hφv n hn]
  have key := hasSum_integral_of_summable_integral_norm (μ := volume.restrict (Set.Ioi (1 : ℝ)))
    (F := fun n x => c n * (φ n x : ℂ)) (fun n => ((hφi n).ofReal).const_mul _)
    (by simpa only [hn] using hs)
  simp only [hv] at key
  rw [key.tsum_eq]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  have hx0 : (0 : ℝ) ≤ x := le_trans zero_le_one (le_of_lt hx)
  simp only
  rw [tsum_eq_sum (s := Finset.Icc 1 ⌊x⌋₊), Finset.sum_mul]
  · apply Finset.sum_congr rfl
    intro n hn
    have : (n : ℝ) ≤ x := (Nat.le_floor_iff hx0).1 (Finset.mem_Icc.1 hn).2
    simp only [hφ]
    rw [Set.indicator_of_mem (show x ∈ Set.Ici (n : ℝ) from this)]
  · intro n hn
    rcases eq_or_ne n 0 with rfl | hn0
    · simp [h0]
    · have : ¬ (n : ℝ) ≤ x := by
        intro h
        exact hn (Finset.mem_Icc.2 ⟨Nat.one_le_iff_ne_zero.2 hn0, (Nat.le_floor_iff hx0).2 h⟩)
      simp only [hφ]
      rw [Set.indicator_of_notMem (show x ∉ Set.Ici (n : ℝ) from this)]
      simp

lemma integral_mul_exp_neg_sq {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun t : ℝ => t * Real.exp (-(t * x))) (Set.Ioi 0) ∧
    ∫ t in Set.Ioi 0, t * Real.exp (-(t * x)) = x ^ (-2 : ℝ) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 2) (r := x) (by norm_num) hx
  have h2 : ∫ t in Set.Ioi 0, t * Real.exp (-(t * x)) = x ^ (-2 : ℝ) := by
    have e : (2 : ℝ) - 1 = 1 := by norm_num
    simp only [e, Real.rpow_one, Real.Gamma_two, mul_one] at h
    simp only [mul_comm _ x]
    rw [h, Real.rpow_neg hx.le, one_div, Real.inv_rpow hx.le]
  refine ⟨Integrable.of_integral_ne_zero ?_, h2⟩
  rw [h2]
  positivity

lemma integral_integral_exp_kernel (A : ℝ → ℂ) (hA : Measurable A) (K : ℝ)
    (hK : ∀ x : ℝ, 1 < x → ‖A x‖ ≤ K * Real.sqrt x) :
    ∫ t in Set.Ioi (0 : ℝ), ∫ x in Set.Ioi (1 : ℝ), A x * ((t * Real.exp (-(t * x)) : ℝ) : ℂ) =
      ∫ x in Set.Ioi (1 : ℝ), A x * (x : ℂ) ^ (-(1 : ℂ) - 1) := by
  have hm : Measurable (Function.uncurry fun (x t : ℝ) => A x * ((t * Real.exp (-(t * x)) : ℝ) : ℂ)) := by
    unfold Function.uncurry
    fun_prop
  have hint : Integrable (Function.uncurry fun (x t : ℝ) => A x * ((t * Real.exp (-(t * x)) : ℝ) : ℂ))
      ((volume.restrict (Set.Ioi (1 : ℝ))).prod (volume.restrict (Set.Ioi (0 : ℝ)))) := by
    rw [integrable_prod_iff hm.aestronglyMeasurable]
    constructor
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx
      exact (Integrable.ofReal (𝕜 := ℂ) (integral_mul_exp_neg_sq hx0).1).const_mul (A x)
    · have hb : IntegrableOn (fun x : ℝ => K * x ^ (-(3 / 2) : ℝ)) (Set.Ioi 1) :=
        (integrableOn_Ioi_rpow_of_lt (by norm_num) zero_lt_one).const_mul K
      refine Integrable.mono' hb (hm.aestronglyMeasurable.norm.integral_prod_right') ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx
      have e : ∫ t in Set.Ioi (0 : ℝ), ‖A x * ((t * Real.exp (-(t * x)) : ℝ) : ℂ)‖ = ‖A x‖ * x ^ (-2 : ℝ) := by
        rw [← (integral_mul_exp_neg_sq hx0).2, ← integral_const_mul]
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t ht
        have ht0 : (0 : ℝ) < t := ht
        simp only
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      simp only [Function.uncurry]
      rw [e, Real.norm_of_nonneg (by positivity)]
      calc ‖A x‖ * x ^ (-2 : ℝ) ≤ K * Real.sqrt x * x ^ (-2 : ℝ) := by
            gcongr; exact hK x hx
        _ = K * x ^ (-(3 / 2) : ℝ) := by
            rw [Real.sqrt_eq_rpow, mul_assoc, ← Real.rpow_add hx0]; norm_num
  rw [← integral_integral_swap hint]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx
  simp only
  rw [integral_const_mul, integral_complex_ofReal, (integral_mul_exp_neg_sq hx0).2,
    Complex.ofReal_cpow hx0.le]
  norm_num

lemma LFam.a_le_mul (𝓕 : LFam) (g : 𝓕.G) (n : ℕ) : 𝓕.a g n ≤ 14 * n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [𝓕.a_zero]
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h := (abs_le.1 (𝓕.count g n hn1)).2
  rw [Nat.floor_natCast] at h
  have h2 : 𝓕.a g n ≤ ∑ m ∈ Finset.Icc 1 n, 𝓕.a g m :=
    Finset.single_le_sum (f := 𝓕.a g) (fun m _ => 𝓕.a_nonneg g m) (Finset.mem_Icc.2 ⟨hn, le_rfl⟩)
  have h3 : Real.sqrt n ≤ n := by
    rw [Real.sqrt_le_left (by positivity)]; nlinarith
  have h4 : 𝓕.κ * n ≤ 4 * n := by gcongr; exact 𝓕.κ_le
  linarith

lemma summable_nat_mul_exp_neg {t : ℝ} (ht : 0 < t) :
    Summable (fun n : ℕ => (n : ℝ) * Real.exp (-(t * n))) := by
  have := Real.summable_pow_mul_exp_neg_nat_mul 1 ht
  simpa using this

lemma LFam.norm_chi (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ) (g : 𝓕.G) : ‖χ g‖ = 1 := by
  simp

lemma LFam.norm_aChi_le (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ) (n : ℕ) : ‖𝓕.aChi χ n‖ ≤ 14 * 𝓕.B * n := by
  unfold LFam.aChi
  calc ‖∑ g, χ g * (𝓕.a g n : ℂ)‖ ≤ ∑ g : 𝓕.G, (14 * n : ℝ) := by
        refine norm_sum_le_of_le _ fun g _ => ?_
        rw [norm_mul, 𝓕.norm_chi, one_mul, Complex.norm_real, Real.norm_of_nonneg (𝓕.a_nonneg g n)]
        exact 𝓕.a_le_mul g n
    _ = Fintype.card 𝓕.G * (14 * n : ℝ) := by simp
    _ ≤ 𝓕.B * (14 * n : ℝ) := by gcongr; exact 𝓕.card_le
    _ = _ := by ring

lemma LFam.res_eq_sum (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ) : 𝓕.res χ = ∑ g, χ g * (𝓕.κ : ℂ) := by
  rw [← Finset.sum_mul, AddChar.sum_eq_ite]
  unfold LFam.res
  by_cases h : χ = 1
  · rw [if_pos h, if_pos (show χ = 0 from h)]; push_cast; ring
  · rw [if_neg h, if_neg (show ¬ χ = 0 from h)]; simp

lemma LFam.summable_norm_aChi_exp (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ) {t : ℝ} (ht : 0 < t) :
    Summable (fun n : ℕ => ‖𝓕.aChi χ n‖ * Real.exp (-(t * n))) := by
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    ((summable_nat_mul_exp_neg ht).mul_left (14 * 𝓕.B))
  rw [← mul_assoc]
  gcongr
  exact 𝓕.norm_aChi_le χ n

lemma LFam.norm_theta_large (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ) {t : ℝ} (ht : 1 ≤ t) :
    ‖∑' n : ℕ, 𝓕.aChi χ n * (Real.exp (-(t * n)) : ℂ)‖ ≤
      (14 * ∑' n : ℕ, (n : ℝ) * Real.exp (-(1 / 2 * n))) * 𝓕.B * Real.exp (-(t / 2)) := by
  have hB : 0 ≤ 𝓕.B := le_trans (by norm_num) 𝓕.B_ge
  have hs := (summable_nat_mul_exp_neg (t := 1 / 2) (by norm_num)).hasSum.mul_left
    (14 * 𝓕.B * Real.exp (-(t / 2)))
  refine (tsum_of_norm_bounded hs fun n => ?_).trans (le_of_eq (by ring))
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have := 𝓕.norm_aChi_le χ 0
    simpa using this
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have : Real.exp (-(t * n)) ≤ Real.exp (-(t / 2)) * Real.exp (-(1 / 2 * n)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    nlinarith
  calc ‖𝓕.aChi χ n‖ * Real.exp (-(t * n))
      ≤ (14 * 𝓕.B * n) * (Real.exp (-(t / 2)) * Real.exp (-(1 / 2 * n))) := by
        gcongr; exact 𝓕.norm_aChi_le χ n
    _ = _ := by ring

lemma LFam.norm_theta_small (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ) {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    ‖∑' n : ℕ, 𝓕.aChi χ n * (Real.exp (-(t * n)) : ℂ) - 𝓕.res χ / t‖ ≤ 𝓕.B ^ 11 * t := by
  have hB : 0 ≤ 𝓕.B := le_trans (by norm_num) 𝓕.B_ge
  have hs : ∀ g, Summable (fun n : ℕ => 𝓕.a g n * Real.exp (-(t * n))) := fun g => by
    refine Summable.of_nonneg_of_le (fun n => mul_nonneg (𝓕.a_nonneg g n) (Real.exp_pos _).le) (fun n => ?_)
      ((summable_nat_mul_exp_neg ht).mul_left 14)
    rw [← mul_assoc]
    gcongr
    exact 𝓕.a_le_mul g n
  have h1 : HasSum (fun n : ℕ => ∑ g, χ g * ((𝓕.a g n * Real.exp (-(t * n)) : ℝ) : ℂ))
      (∑ g, χ g * ((∑' n : ℕ, 𝓕.a g n * Real.exp (-(t * n)) : ℝ) : ℂ)) :=
    hasSum_sum fun g _ => (Complex.hasSum_ofReal.2 (hs g).hasSum).mul_left _
  have h2 : ∀ n : ℕ, 𝓕.aChi χ n * (Real.exp (-(t * n)) : ℂ) =
      ∑ g, χ g * ((𝓕.a g n * Real.exp (-(t * n)) : ℝ) : ℂ) := fun n => by
    unfold LFam.aChi
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [Complex.ofReal_mul, mul_assoc]
  simp only [h2]
  rw [h1.tsum_eq, 𝓕.res_eq_sum, Finset.sum_div, ← Finset.sum_sub_distrib]
  calc _ ≤ ∑ g : 𝓕.G, 𝓕.B ^ 10 * t := by
        refine norm_sum_le_of_le _ fun g _ => ?_
        rw [mul_div_assoc, ← mul_sub, norm_mul, 𝓕.norm_chi, one_mul, ← Complex.ofReal_div,
          ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
        exact 𝓕.theta g t ht ht1
    _ = Fintype.card 𝓕.G * (𝓕.B ^ 10 * t) := by simp
    _ ≤ 𝓕.B * (𝓕.B ^ 10 * t) := by gcongr; exact 𝓕.card_le
    _ = _ := by ring

lemma LFam.norm_sum_aChi_sub_le (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ) {x : ℝ} (hx : 1 ≤ x) :
    ‖∑ n ∈ Finset.Icc 1 ⌊x⌋₊, 𝓕.aChi χ n - 𝓕.res χ * x‖ ≤ 10 * 𝓕.B * Real.sqrt x := by
  unfold LFam.aChi
  rw [Finset.sum_comm, 𝓕.res_eq_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  calc _ ≤ ∑ g : 𝓕.G, 10 * Real.sqrt x := by
        refine norm_sum_le_of_le _ fun g _ => ?_
        rw [← Finset.mul_sum, mul_assoc, ← mul_sub, norm_mul, 𝓕.norm_chi, one_mul, ← Complex.ofReal_sum,
          ← Complex.ofReal_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
        exact 𝓕.count g x hx
    _ = Fintype.card 𝓕.G * (10 * Real.sqrt x) := by simp
    _ ≤ 𝓕.B * (10 * Real.sqrt x) := by gcongr; exact 𝓕.card_le
    _ = _ := by ring

lemma LFam.integral_theta (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ) (hχ : χ ≠ 1) :
    ∫ t in Set.Ioi (0 : ℝ), ∑' n : ℕ, 𝓕.aChi χ n * (Real.exp (-(t * n)) : ℂ) = 𝓕.F χ 1 := by
  have hr : 𝓕.res χ = 0 := by unfold LFam.res; rw [if_neg hχ]
  have h0 : 𝓕.aChi χ 0 = 0 := by simp [LFam.aChi, 𝓕.a_zero]
  have hm : Measurable fun x : ℝ => ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, 𝓕.aChi χ n :=
    (measurable_from_top (f := fun k : ℕ => ∑ n ∈ Finset.Icc 1 k, 𝓕.aChi χ n)).comp Nat.measurable_floor
  have h := integral_integral_exp_kernel _ hm (10 * 𝓕.B) (fun x hx => by
    have := 𝓕.norm_sum_aChi_sub_le χ hx.le
    rwa [hr, zero_mul, sub_zero] at this)
  unfold LFam.F LFam.mel
  rw [if_neg hχ, one_mul]
  simp only [hr, zero_mul, sub_zero]
  rw [← h]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  exact tsum_exp_eq_integral _ h0 ht (𝓕.summable_norm_aChi_exp χ ht)

theorem LFam.exp_sum_bounds : ∃ C : ℝ, 0 < C ∧ ∀ (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ), (∀ t : ℝ, 0 < t → Summable (fun n : ℕ => ‖𝓕.aChi χ n‖ * Real.exp (-(t * n))) ∧ ‖∑' n : ℕ, 𝓕.aChi χ n * (Real.exp (-(t * n)) : ℂ) - 𝓕.res χ / t‖ ≤ C * 𝓕.B ^ 11 * min t (1 / t)) ∧ (χ ≠ 1 → (∀ t : ℝ, 1 ≤ t → ‖∑' n : ℕ, 𝓕.aChi χ n * (Real.exp (-(t * n)) : ℂ)‖ ≤ C * 𝓕.B * Real.exp (-(t / 2))) ∧ ∫ t in Set.Ioi (0 : ℝ), ∑' n : ℕ, 𝓕.aChi χ n * (Real.exp (-(t * n)) : ℂ) = 𝓕.F χ 1) := by
  set S : ℝ := 14 * ∑' n : ℕ, (n : ℝ) * Real.exp (-(1 / 2 * n)) with hS
  have hS0 : 0 ≤ S := mul_nonneg (by norm_num) (tsum_nonneg fun n => by positivity)
  refine ⟨2 * S + 4, by positivity, fun 𝓕 χ => ⟨fun t ht => ⟨𝓕.summable_norm_aChi_exp χ ht, ?_⟩,
    fun hχ => ⟨fun t ht => ?_, 𝓕.integral_theta χ hχ⟩⟩⟩
  · have hB : 1 ≤ 𝓕.B := le_trans (by norm_num) 𝓕.B_ge
    rcases le_total t 1 with h1 | h1
    · have : t ≤ 1 / t := by rw [le_div_iff₀ ht]; nlinarith
      rw [min_eq_left this]
      refine (𝓕.norm_theta_small χ ht h1).trans ?_
      have : 0 ≤ 𝓕.B ^ 11 * t := by positivity
      nlinarith
    · have : 1 / t ≤ t := by rw [div_le_iff₀ ht]; nlinarith
      rw [min_eq_right this]
      have e1 : Real.exp (-(t / 2)) ≤ 2 * (1 / t) := by
        have := Real.add_one_le_exp (t / 2)
        rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by positivity)]
        have e : (2 * (1 / t))⁻¹ = t / 2 := by field_simp
        linarith
      have hκ : 0 ≤ 𝓕.κ := le_trans (by positivity) 𝓕.κ_ge
      have e2 : ‖𝓕.res χ‖ ≤ 4 * 𝓕.B := by
        unfold LFam.res
        split_ifs
        · rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
          exact mul_le_mul 𝓕.κ_le 𝓕.card_le (by positivity) (by norm_num)
        · rw [norm_zero]; positivity
      have e3 : 𝓕.B ≤ 𝓕.B ^ 11 := le_self_pow₀ hB (by norm_num)
      calc _ ≤ S * 𝓕.B * Real.exp (-(t / 2)) + ‖𝓕.res χ‖ * (1 / t) := by
            refine (norm_sub_le _ _).trans (add_le_add (𝓕.norm_theta_large χ h1) (le_of_eq ?_))
            rw [norm_div, Complex.norm_real, Real.norm_of_nonneg ht.le, mul_one_div]
        _ ≤ S * 𝓕.B * (2 * (1 / t)) + 4 * 𝓕.B * (1 / t) := by gcongr
        _ = (2 * S + 4) * 𝓕.B * (1 / t) := by ring
        _ ≤ _ := by gcongr
  · have hB : 0 ≤ 𝓕.B := le_trans (by norm_num) 𝓕.B_ge
    refine (𝓕.norm_theta_large χ ht).trans ?_
    gcongr
    linarith

end GlobalTheory.Hk
