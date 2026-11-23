import Mathlib

open Filter Topology MeasureTheory Set
open scoped Real

namespace GlobalTheory.KroneckerLimit

private theorem le_apply_zero_of_monotoneOn_Iic_antitoneOn_Ici {f : ℝ → ℝ} (hm : MonotoneOn f (Iic 0))
    (ha : AntitoneOn f (Ici 0)) (t : ℝ) : f t ≤ f 0 := by
  rcases le_total t 0 with h | h
  · exact hm (Set.mem_Iic.2 h) (Set.mem_Iic.2 le_rfl) h
  · exact ha (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 h) h

theorem abs_sum_range_sub_integral_le {f : ℝ → ℝ} (h0 : ∀ t, 0 ≤ f t) (hc : Continuous f)
    (hm : MonotoneOn f (Iic 0)) (ha : AntitoneOn f (Ici 0)) (x : ℝ) (k : ℕ) :
    |∑ i ∈ Finset.range k, f (x + i) - ∫ t in x..x + k, f t| ≤ f 0 := by
  have htop : ∀ t, f t ≤ f 0 := fun t => le_apply_zero_of_monotoneOn_Iic_antitoneOn_Ici hm ha t
  have hbd : ∀ (a lo hi : ℝ), (∀ t ∈ Icc a (a + 1), lo ≤ f t ∧ f t ≤ hi) →
      lo ≤ ∫ t in a..a + 1, f t ∧ ∫ t in a..a + 1, f t ≤ hi := by
    intro a lo hi h
    have hab : a ≤ a + 1 := by linarith
    constructor
    · have := intervalIntegral.integral_mono_on (μ := volume) hab (continuous_const.intervalIntegrable _ _)
        (hc.intervalIntegrable _ _) (fun t ht => (h t ht).1)
      simpa using this
    · have := intervalIntegral.integral_mono_on (μ := volume) hab (hc.intervalIntegrable _ _)
        (continuous_const.intervalIntegrable _ _) (fun t ht => (h t ht).2)
      simpa using this
  obtain ⟨D, hD⟩ : ∃ D : ℕ → ℝ, ∀ j : ℕ,
      D j = ∑ i ∈ Finset.range j, f (x + i) - ∫ t in x..x + j, f t := ⟨_, fun j => rfl⟩
  have hstep : ∀ j : ℕ, D (j + 1) = D j + (f (x + j) - ∫ t in (x + j)..(x + j + 1), f t) := by
    intro j
    rw [hD, hD, show x + ((j + 1 : ℕ) : ℝ) = x + j + 1 by push_cast; ring, Finset.sum_range_succ,
      ← intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable x (x + j))
        (hc.intervalIntegrable (x + j) (x + j + 1))]
    ring
  have key : ∀ j : ℕ, (x + j ≤ 0 → D j ≤ 0) ∧ D j + f (x + j) ≤ f 0 ∧ -f 0 ≤ D j ∧
      (x + j ≤ 0 → -f (x + j) ≤ D j) := by
    intro j
    induction j with
    | zero =>
      have hD0 : D 0 = 0 := by simp [hD]
      simp only [Nat.cast_zero, add_zero, hD0]
      exact ⟨fun _ => le_rfl, by linarith [htop x], by linarith [h0 0], fun _ => by linarith [h0 x]⟩
    | succ j ih =>
      obtain ⟨ih1, ih2, ih3, ih4⟩ := ih
      rw [hstep j, show x + ((j + 1 : ℕ) : ℝ) = x + j + 1 by push_cast; ring]
      rcases le_or_gt (x + j + 1) 0 with hl | hl
      · obtain ⟨hb1, hb2⟩ := hbd (x + j) (f (x + j)) (f (x + j + 1)) (fun t ht =>
          ⟨hm (Set.mem_Iic.2 (by linarith)) (Set.mem_Iic.2 (by linarith [ht.2])) ht.1,
           hm (Set.mem_Iic.2 (by linarith [ht.2])) (Set.mem_Iic.2 hl) ht.2⟩)
        have e1 := ih1 (by linarith)
        have e4 := ih4 (by linarith)
        refine ⟨fun _ => by linarith, by linarith [htop (x + j + 1)],
          by linarith [htop (x + j + 1)], fun _ => by linarith⟩
      · rcases le_or_gt 0 (x + j) with hr | hr
        · obtain ⟨hb1, hb2⟩ := hbd (x + j) (f (x + j + 1)) (f (x + j)) (fun t ht =>
            ⟨ha (Set.mem_Ici.2 (by linarith [ht.1])) (Set.mem_Ici.2 (by linarith)) ht.2,
             ha (Set.mem_Ici.2 hr) (Set.mem_Ici.2 (by linarith [ht.1])) ht.1⟩)
          refine ⟨fun h => by linarith, by linarith, by linarith, fun h => by linarith⟩
        · obtain ⟨hb1, hb2⟩ := hbd (x + j) (f (x + j) + f (x + j + 1) - f 0) (f 0) (fun t ht => by
            refine ⟨?_, htop t⟩
            rcases le_total t 0 with h | h
            · have := hm (Set.mem_Iic.2 hr.le) (Set.mem_Iic.2 h) ht.1
              linarith [htop (x + j + 1)]
            · have := ha (Set.mem_Ici.2 h) (Set.mem_Ici.2 hl.le) ht.2
              linarith [htop (x + j)])
          have e1 := ih1 hr.le
          have e4 := ih4 hr.le
          refine ⟨fun h => by linarith, by linarith, by linarith, fun h => by linarith⟩
  obtain ⟨-, h2, h3, -⟩ := key k
  rw [hD] at h2 h3
  rw [abs_le]
  exact ⟨h3, by linarith [h0 (x + k)]⟩

theorem summable_and_abs_tsum_sub_integral_le {f : ℝ → ℝ} (h0 : ∀ t, 0 ≤ f t) (hc : Continuous f)
    (hm : MonotoneOn f (Iic 0)) (ha : AntitoneOn f (Ici 0)) (hi : Integrable f) (a : ℝ) :
    Summable (fun n : ℤ => f (a + n)) ∧ |∑' n : ℤ, f (a + n) - ∫ t, f t| ≤ f 0 := by
  have htop : ∀ t, f t ≤ f 0 := fun t => le_apply_zero_of_monotoneOn_Iic_antitoneOn_Ici hm ha t
  have hfin : ∀ N : ℕ, ∑ i ∈ Finset.range (2 * N), f (a - N + i) ≤ (∫ t, f t) + f 0 ∧
      ∫ t in (a - N)..(a + N), f t ≤ ∑ i ∈ Finset.range (2 * N), f (a - N + i) + f 0 := by
    intro N
    have h := abs_le.1 (abs_sum_range_sub_integral_le h0 hc hm ha (a - N) (2 * N))
    have he : a - N + ((2 * N : ℕ) : ℝ) = a + N := by push_cast; ring
    rw [he] at h
    have hle : ∫ t in (a - N)..(a + N), f t ≤ ∫ t, f t := by
      rw [intervalIntegral.integral_of_le (by linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)])]
      exact setIntegral_le_integral hi (Filter.Eventually.of_forall fun t => h0 t)
    obtain ⟨hl1, hl2⟩ := h
    constructor <;> linarith
  have himg : ∀ N : ℕ, ∑ n ∈ (Finset.range (2 * N)).image (fun i : ℕ => (i : ℤ) - N), f (a + n) =
      ∑ i ∈ Finset.range (2 * N), f (a - N + i) := by
    intro N
    rw [Finset.sum_image (by intro i _ j _ h; simpa using h)]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    push_cast
    ring
  have hset : ∀ s : Finset ℤ, ∃ N : ℕ,
      s ⊆ (Finset.range (2 * N)).image (fun i : ℕ => (i : ℤ) - N) := by
    intro s
    obtain ⟨S, hS⟩ : ∃ S : ℕ, S = ∑ m ∈ s, m.natAbs := ⟨_, rfl⟩
    refine ⟨S + 1, fun n hn => ?_⟩
    have hle : n.natAbs ≤ S := hS ▸
      Finset.single_le_sum (f := fun m : ℤ => m.natAbs) (fun _ _ => Nat.zero_le _) hn
    rw [Finset.mem_image]
    refine ⟨(n + ((S + 1 : ℕ) : ℤ)).toNat, ?_, ?_⟩
    · rw [Finset.mem_range]
      omega
    · omega
  have hbound : ∀ s : Finset ℤ, ∑ n ∈ s, f (a + n) ≤ (∫ t, f t) + f 0 := by
    intro s
    obtain ⟨N, hN⟩ := hset s
    have := Finset.sum_le_sum_of_subset_of_nonneg hN (fun n _ _ => h0 (a + n))
    rw [himg N] at this
    linarith [(hfin N).1]
  have hsum : Summable (fun n : ℤ => f (a + n)) := summable_of_sum_le (fun n => h0 _) hbound
  refine ⟨hsum, abs_le.2 ⟨?_, ?_⟩⟩
  · have hbot : Tendsto (fun N : ℕ => a - (N : ℝ)) atTop atBot :=
      tendsto_atBot.2 fun b => eventually_atTop.2 ⟨⌈a - b⌉₊, fun N hN => by
        have h1 := Nat.le_ceil (a - b)
        have h2 : ((⌈a - b⌉₊ : ℕ) : ℝ) ≤ N := by exact_mod_cast hN
        linarith⟩
    have htop' : Tendsto (fun N : ℕ => a + (N : ℝ)) atTop atTop :=
      tendsto_atTop.2 fun b => eventually_atTop.2 ⟨⌈b - a⌉₊, fun N hN => by
        have h1 := Nat.le_ceil (b - a)
        have h2 : ((⌈b - a⌉₊ : ℕ) : ℝ) ≤ N := by exact_mod_cast hN
        linarith⟩
    have hlim := intervalIntegral_tendsto_integral hi hbot htop'
    have : ∫ t, f t ≤ ∑' n : ℤ, f (a + n) + f 0 := le_of_tendsto' hlim fun N => by
      show ∫ t in (a - N)..(a + N), f t ≤ _
      have h1 := (hfin N).2
      have h2 := hsum.sum_le_tsum ((Finset.range (2 * N)).image (fun i : ℕ => (i : ℤ) - N))
        (fun n _ => h0 _)
      rw [himg N] at h2
      linarith
    linarith
  · have := Real.tsum_le_of_sum_le (fun n => h0 _) hbound
    linarith

noncomputable def betaConst (s : ℝ) : ℝ := √π * Real.Gamma (s - 1 / 2) / Real.Gamma s

private theorem integral_rpow_mul_exp_neg_sq_add_mul_eq {Y s u : ℝ} (hu : 0 < u) :
    ∫ t : ℝ, u ^ (s - 1) * Real.exp (-((t ^ 2 + Y ^ 2) * u)) =
      √π * (u ^ (s - 1 / 2 - 1) * Real.exp (-(Y ^ 2 * u))) := by
  have h : (fun t : ℝ => u ^ (s - 1) * Real.exp (-((t ^ 2 + Y ^ 2) * u))) =
      fun t : ℝ => (u ^ (s - 1) * Real.exp (-(Y ^ 2 * u))) * Real.exp (-u * t ^ 2) := by
    funext t
    rw [show -((t ^ 2 + Y ^ 2) * u) = -(Y ^ 2 * u) + -u * t ^ 2 by ring, Real.exp_add]
    ring
  rw [h, integral_const_mul, integral_gaussian, Real.sqrt_div Real.pi_pos.le,
    show s - 1 / 2 - 1 = (s - 1) - 1 / 2 by ring, Real.rpow_sub hu (s - 1) (1 / 2), Real.sqrt_eq_rpow u]
  ring

private theorem integral_Ioi_rpow_mul_exp_neg_eq_rpow_mul_Gamma {Y s t : ℝ} (hY : 0 < Y) (hs : 0 < s) :
    ∫ u in Ioi (0 : ℝ), u ^ (s - 1) * Real.exp (-((t ^ 2 + Y ^ 2) * u)) =
      (t ^ 2 + Y ^ 2) ^ (-s) * Real.Gamma s := by
  have hp : 0 < t ^ 2 + Y ^ 2 := by positivity
  rw [Real.integral_rpow_mul_exp_neg_mul_Ioi hs hp, one_div, Real.inv_rpow hp.le,
    Real.rpow_neg hp.le]

private theorem integrable_uncurry_rpow_mul_exp_neg_sq_add {Y s : ℝ} (hY : 0 < Y) (hs : 1 / 2 < s) :
    Integrable (Function.uncurry fun u t : ℝ => u ^ (s - 1) * Real.exp (-((t ^ 2 + Y ^ 2) * u)))
      ((volume.restrict (Ioi (0 : ℝ))).prod volume) := by
  have hmeas : Measurable fun p : ℝ × ℝ => p.1 ^ (s - 1) * Real.exp (-((p.2 ^ 2 + Y ^ 2) * p.1)) := by
    fun_prop
  refine (integrable_prod_iff hmeas.aestronglyMeasurable).2 ⟨?_, ?_⟩
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun u hu => ?_)
    have h : (fun t : ℝ => u ^ (s - 1) * Real.exp (-((t ^ 2 + Y ^ 2) * u))) =
        fun t : ℝ => (u ^ (s - 1) * Real.exp (-(Y ^ 2 * u))) * Real.exp (-u * t ^ 2) := by
      funext t
      rw [show -((t ^ 2 + Y ^ 2) * u) = -(Y ^ 2 * u) + -u * t ^ 2 by ring, Real.exp_add]
      ring
    rw [h]
    exact (integrable_exp_neg_mul_sq hu).const_mul _
  · have hI := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := s - 1 / 2 - 1) (b := Y ^ 2)
      (by linarith) one_pos (by positivity)
    simp only [Real.rpow_one, neg_mul] at hI
    refine IntegrableOn.congr_fun (hI.const_mul √π) (fun u hu => ?_) measurableSet_Ioi
    have hu' : 0 < u := hu
    try dsimp only
    rw [← integral_rpow_mul_exp_neg_sq_add_mul_eq hu']
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    try dsimp only
    rw [Real.norm_of_nonneg (by positivity)]

theorem integrable_rpow_sq_add {Y s : ℝ} (hY : 0 < Y) (hs : 1 ≤ s) :
    Integrable (fun t : ℝ => (t ^ 2 + Y ^ 2) ^ (-s)) := by
  have hK := integrable_uncurry_rpow_mul_exp_neg_sq_add hY (by linarith : 1 / 2 < s)
  have hΓ : 0 < Real.Gamma s := Real.Gamma_pos_of_pos (by linarith)
  have h := hK.integral_prod_right
  simp only [Function.uncurry_apply_pair] at h
  have h' : Integrable (fun t : ℝ => (t ^ 2 + Y ^ 2) ^ (-s) * Real.Gamma s) := by
    refine h.congr (Filter.Eventually.of_forall fun t => ?_)
    exact integral_Ioi_rpow_mul_exp_neg_eq_rpow_mul_Gamma hY (by linarith)
  have := h'.div_const (Real.Gamma s)
  simpa [hΓ.ne'] using this

theorem integral_rpow_sq_add {Y s : ℝ} (hY : 0 < Y) (hs : 1 / 2 < s) :
    ∫ t : ℝ, (t ^ 2 + Y ^ 2) ^ (-s) = betaConst s * Y ^ (1 - 2 * s) := by
  have hΓ : 0 < Real.Gamma s := Real.Gamma_pos_of_pos (by linarith)
  have hK := integrable_uncurry_rpow_mul_exp_neg_sq_add hY hs
  have hswap := integral_integral_swap hK
  have hB : ∫ u in Ioi (0 : ℝ), ∫ t : ℝ, u ^ (s - 1) * Real.exp (-((t ^ 2 + Y ^ 2) * u)) =
      √π * ((1 / Y ^ 2) ^ (s - 1 / 2) * Real.Gamma (s - 1 / 2)) := by
    rw [setIntegral_congr_fun measurableSet_Ioi (fun u hu => integral_rpow_mul_exp_neg_sq_add_mul_eq (s := s) (Y := Y) hu),
      integral_const_mul, Real.integral_rpow_mul_exp_neg_mul_Ioi (by linarith) (by positivity)]
  have hA : ∀ t : ℝ, ∫ u in Ioi (0 : ℝ), u ^ (s - 1) * Real.exp (-((t ^ 2 + Y ^ 2) * u)) =
      (t ^ 2 + Y ^ 2) ^ (-s) * Real.Gamma s := fun t => integral_Ioi_rpow_mul_exp_neg_eq_rpow_mul_Gamma hY (by linarith)
  simp only [hA, hB, integral_mul_const] at hswap
  have hY2 : (1 / Y ^ 2) ^ (s - 1 / 2) = Y ^ (1 - 2 * s) := by
    rw [one_div, Real.inv_rpow (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul hY.le,
      ← Real.rpow_neg hY.le]
    congr 1
    push_cast
    ring
  rw [hY2] at hswap
  unfold betaConst
  rw [show √π * Real.Gamma (s - 1 / 2) / Real.Gamma s * Y ^ (1 - 2 * s) =
      √π * (Y ^ (1 - 2 * s) * Real.Gamma (s - 1 / 2)) / Real.Gamma s by ring, hswap,
    mul_div_assoc, div_self hΓ.ne', mul_one]

theorem betaConst_one : betaConst 1 = π := by
  unfold betaConst
  rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num, Real.Gamma_one_half_eq, Real.Gamma_one, div_one,
    Real.mul_self_sqrt Real.pi_pos.le]

theorem hasDerivAt_betaConst_one : HasDerivAt betaConst (-2 * π * Real.log 2) 1 := by
  have h1 : HasDerivAt Real.Gamma (-√π * (Real.eulerMascheroniConstant + 2 * Real.log 2)) (1 - 1 / 2) := by
    convert Real.hasDerivAt_Gamma_one_half using 1
    norm_num
  have h2 := ((h1.comp_sub_const 1 (1 / 2)).const_mul √π).div Real.hasDerivAt_Gamma_one
    (by rw [Real.Gamma_one]; exact one_ne_zero)
  have hp := Real.mul_self_sqrt Real.pi_pos.le
  have hf : betaConst = (fun y => √π * Real.Gamma (y - 1 / 2)) / Real.Gamma := by
    funext y
    rfl
  rw [hf]
  refine h2.congr_deriv ?_
  rw [Real.Gamma_one, show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num, Real.Gamma_one_half_eq]
  linear_combination (-(2 * Real.log 2)) * hp

end GlobalTheory.KroneckerLimit
