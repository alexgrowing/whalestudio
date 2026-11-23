import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LamIdealOfNotPrimePow
open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical

namespace GlobalTheory.Hk

theorem unimodal_sum_integral (f : ℝ → ℝ) (h0 : ∀ t, 0 ≤ f t)
    (hf : ∀ s t, |s| ≤ |t| → f t ≤ f s) (x₀ : ℝ) (n : ℕ) :
    |∑ i ∈ Finset.range n, f (x₀ + i) - ∫ t in x₀..x₀ + n, f t| ≤ f 0 := by
  have hmono : MonotoneOn f (Set.Iic 0) := by
    intro s hs t ht hst
    apply hf
    rw [abs_of_nonpos (Set.mem_Iic.mp ht), abs_of_nonpos (Set.mem_Iic.mp hs)]
    linarith
  have hanti : AntitoneOn f (Set.Ici 0) := by
    intro s hs t ht hst
    apply hf
    rw [abs_of_nonneg (Set.mem_Ici.mp hs), abs_of_nonneg (Set.mem_Ici.mp ht)]
    exact hst
  have hI0 : ∀ a : ℝ, IntervalIntegrable f MeasureTheory.volume a 0 := by
    intro a
    rcases le_total a 0 with ha | ha
    · apply MonotoneOn.intervalIntegrable
      apply hmono.mono
      rw [Set.uIcc_of_le ha]
      exact Set.Icc_subset_Iic_self
    · apply AntitoneOn.intervalIntegrable
      apply hanti.mono
      rw [Set.uIcc_of_ge ha]
      exact Set.Icc_subset_Ici_self
  have hI : ∀ a b : ℝ, IntervalIntegrable f MeasureTheory.volume a b :=
    fun a b => (hI0 a).trans (hI0 b).symm
  have hle0 : ∀ t, f t ≤ f 0 := fun t => hf 0 t (by simp)
  obtain ⟨G, hG⟩ : ∃ G : ℝ → ℝ, ∀ y, G y = f (min y 0) := ⟨_, fun _ => rfl⟩
  obtain ⟨H, hH⟩ : ∃ H : ℝ → ℝ, ∀ y, H y = f (max y 0) := ⟨_, fun _ => rfl⟩
  have hPA : ∀ p t, p ≤ t → t ≤ p + 1 → f t ≤ f p + (G (p + 1) - G p) := by
    intro p t hpt htq
    rw [hG, hG]
    rcases le_total 0 p with hp | hp
    · rw [min_eq_right hp, min_eq_right (by linarith : (0:ℝ) ≤ p + 1)]
      have : f t ≤ f p := hf p t (by
        rw [abs_of_nonneg hp, abs_of_nonneg (by linarith : (0:ℝ) ≤ t)]; exact hpt)
      linarith
    · rw [min_eq_left hp]
      rcases le_total (p + 1) 0 with hq | hq
      · rw [min_eq_left hq]
        have : f t ≤ f (p + 1) := hf (p + 1) t (by
          rw [abs_of_nonpos hq, abs_of_nonpos (by linarith : t ≤ 0)]; linarith)
        linarith
      · rw [min_eq_right hq]
        have := hle0 t
        linarith
  have hPB : ∀ p t, p ≤ t → t ≤ p + 1 → f p - (H p - H (p + 1)) ≤ f t := by
    intro p t hpt htq
    rw [hH, hH]
    rcases le_total 0 p with hp | hp
    · rw [max_eq_left hp, max_eq_left (by linarith : (0:ℝ) ≤ p + 1)]
      have : f (p + 1) ≤ f t := hf t (p + 1) (by
        rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ t), abs_of_nonneg (by linarith : (0:ℝ) ≤ p + 1)]
        exact htq)
      linarith
    · rw [max_eq_right hp]
      rcases le_total (p + 1) 0 with hq | hq
      · rw [max_eq_right hq]
        have : f p ≤ f t := hf t p (by
          rw [abs_of_nonpos (by linarith : t ≤ 0), abs_of_nonpos hp]; linarith)
        linarith
      · rw [max_eq_left hq]
        have h1 := hle0 p
        have h2 := hle0 (p + 1)
        rcases le_total t 0 with ht | ht
        · have : f p ≤ f t := hf t p (by rw [abs_of_nonpos ht, abs_of_nonpos hp]; linarith)
          linarith
        · have : f (p + 1) ≤ f t := hf t (p + 1) (by
            rw [abs_of_nonneg ht, abs_of_nonneg hq]; linarith)
          linarith
  have hA : ∀ p, ∫ t in p..p + 1, f t ≤ f p + (G (p + 1) - G p) := by
    intro p
    have := intervalIntegral.integral_mono_on (by linarith : p ≤ p + 1) (hI p (p + 1))
      intervalIntegrable_const (fun t ht => hPA p t ht.1 ht.2)
    rw [intervalIntegral.integral_const, show p + 1 - p = 1 by ring, one_smul] at this
    exact this
  have hB : ∀ p, f p - (H p - H (p + 1)) ≤ ∫ t in p..p + 1, f t := by
    intro p
    have := intervalIntegral.integral_mono_on (by linarith : p ≤ p + 1) intervalIntegrable_const
      (hI p (p + 1)) (fun t ht => hPB p t ht.1 ht.2)
    rw [intervalIntegral.integral_const, show p + 1 - p = 1 by ring, one_smul] at this
    exact this
  have hsplit := intervalIntegral.sum_integral_adjacent_intervals (μ := MeasureTheory.volume)
    (f := f) (a := fun i : ℕ => x₀ + (i : ℝ)) (n := n) (fun k _ => hI _ _)
  simp only [Nat.cast_zero, add_zero, Nat.cast_succ, ← add_assoc] at hsplit
  rw [← hsplit]
  have tG : ∑ i ∈ Finset.range n, (G (x₀ + i + 1) - G (x₀ + i)) = G (x₀ + n) - G x₀ := by
    have := Finset.sum_range_sub (fun i : ℕ => G (x₀ + i)) n
    simpa [Nat.cast_succ, add_assoc] using this
  have tH : ∑ i ∈ Finset.range n, (H (x₀ + i) - H (x₀ + i + 1)) = H x₀ - H (x₀ + n) := by
    have := Finset.sum_range_sub' (fun i : ℕ => H (x₀ + i)) n
    simpa [Nat.cast_succ, add_assoc] using this
  have hG0 : G (x₀ + n) ≤ f 0 := by rw [hG]; exact hle0 _
  have hG1 : 0 ≤ G x₀ := by rw [hG]; exact h0 _
  have hH0 : H x₀ ≤ f 0 := by rw [hH]; exact hle0 _
  have hH1 : 0 ≤ H (x₀ + n) := by rw [hH]; exact h0 _
  rw [abs_sub_le_iff]
  constructor
  · have : (∑ i ∈ Finset.range n, f (x₀ + i)) - (∑ i ∈ Finset.range n, ∫ t in x₀ + i..x₀ + i + 1, f t)
        ≤ ∑ i ∈ Finset.range n, (H (x₀ + i) - H (x₀ + i + 1)) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_le_sum
      intro i _
      have := hB (x₀ + i)
      linarith
    linarith
  · have : (∑ i ∈ Finset.range n, ∫ t in x₀ + i..x₀ + i + 1, f t) - (∑ i ∈ Finset.range n, f (x₀ + i))
        ≤ ∑ i ∈ Finset.range n, (G (x₀ + i + 1) - G (x₀ + i)) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_le_sum
      intro i _
      have := hA (x₀ + i)
      linarith
    linarith

theorem integral_sqrt_one_sub_sq_wide (a b : ℝ) (ha : a ≤ -1) (hb : 1 ≤ b) :
    ∫ t in a..b, Real.sqrt (1 - t ^ 2) = Real.pi / 2 := by
  have hc : Continuous (fun t : ℝ => Real.sqrt (1 - t ^ 2)) := by fun_prop
  have hi : ∀ p q : ℝ, IntervalIntegrable (fun t : ℝ => Real.sqrt (1 - t ^ 2))
      MeasureTheory.volume p q := fun p q => hc.intervalIntegrable p q
  rw [← intervalIntegral.integral_add_adjacent_intervals (hi a (-1)) (hi (-1) b),
    ← intervalIntegral.integral_add_adjacent_intervals (hi (-1) 1) (hi 1 b), integral_sqrt_one_sub_sq]
  have z1 : ∫ t in a..(-1), Real.sqrt (1 - t ^ 2) = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0:ℝ))]
    · simp
    · intro t ht
      rw [Set.uIcc_of_le ha] at ht
      apply Real.sqrt_eq_zero'.mpr
      nlinarith [ht.1, ht.2]
  have z2 : ∫ t in (1:ℝ)..b, Real.sqrt (1 - t ^ 2) = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0:ℝ))]
    · simp
    · intro t ht
      rw [Set.uIcc_of_le hb] at ht
      apply Real.sqrt_eq_zero'.mpr
      nlinarith [ht.1, ht.2]
  rw [z1, z2]
  ring

theorem integral_ellipse_width (α γ x a b : ℝ) (hα : 0 < α) (hγ : 0 < γ) (hx : 0 < x)
    (ha : a ≤ -Real.sqrt (x / γ)) (hb : Real.sqrt (x / γ) ≤ b) :
    ∫ t in a..b, 2 * Real.sqrt ((x - γ * t ^ 2) / α) = Real.pi / Real.sqrt (α * γ) * x := by
  have hxγ : 0 < x / γ := div_pos hx hγ
  have hr : 0 < Real.sqrt (x / γ) := Real.sqrt_pos.mpr hxγ
  have hr2 : Real.sqrt (x / γ) ^ 2 = x / γ := Real.sq_sqrt hxγ.le
  have key : ∀ t : ℝ, 2 * Real.sqrt ((x - γ * t ^ 2) / α)
      = (2 * Real.sqrt (x / α)) * Real.sqrt (1 - (t / Real.sqrt (x / γ)) ^ 2) := by
    intro t
    have e : (x - γ * t ^ 2) / α = (x / α) * (1 - (t / Real.sqrt (x / γ)) ^ 2) := by
      rw [div_pow, hr2]
      field_simp
    rw [e, Real.sqrt_mul (div_nonneg hx.le hα.le)]
    ring
  simp_rw [key]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_div (fun u => Real.sqrt (1 - u ^ 2)) hr.ne',
    integral_sqrt_one_sub_sq_wide]
  · rw [smul_eq_mul]
    have hs : Real.sqrt (x / α) * Real.sqrt (x / γ) = x / Real.sqrt (α * γ) := by
      rw [← Real.sqrt_mul (div_nonneg hx.le hα.le),
        show x / α * (x / γ) = x ^ 2 / (α * γ) by field_simp,
        Real.sqrt_div (sq_nonneg x), Real.sqrt_sq hx.le]
    calc 2 * Real.sqrt (x / α) * (Real.sqrt (x / γ) * (Real.pi / 2))
        = Real.pi * (Real.sqrt (x / α) * Real.sqrt (x / γ)) := by ring
      _ = Real.pi / Real.sqrt (α * γ) * x := by rw [hs]; ring
  · rw [div_le_iff₀ hr]; linarith
  · rw [le_div_iff₀ hr]; linarith

theorem row_count (α c y : ℝ) (hα : 0 < α) :
    ∃ F : Finset ℤ, (∀ m : ℤ, m ∈ F ↔ α * (m + c) ^ 2 ≤ y) ∧
      |(F.card : ℝ) - 2 * Real.sqrt (y / α)| ≤ 1 := by
  rcases lt_or_ge y 0 with hy | hy
  · refine ⟨∅, fun m => ?_, ?_⟩
    · simp only [Finset.notMem_empty, false_iff, not_le]
      have := mul_nonneg hα.le (sq_nonneg ((m : ℝ) + c))
      linarith
    · rw [Real.sqrt_eq_zero'.mpr (div_nonpos_of_nonpos_of_nonneg hy.le hα.le)]
      simp
  · have hyα : 0 ≤ y / α := div_nonneg hy hα.le
    refine ⟨Finset.Icc ⌈-c - Real.sqrt (y / α)⌉ ⌊-c + Real.sqrt (y / α)⌋, fun m => ?_, ?_⟩
    · rw [Finset.mem_Icc, Int.ceil_le, Int.le_floor,
        show α * ((m : ℝ) + c) ^ 2 ≤ y ↔ ((m : ℝ) + c) ^ 2 ≤ y / α by
          rw [le_div_iff₀ hα, mul_comm],
        Real.sq_le hyα]
      constructor
      · rintro ⟨h1, h2⟩; constructor <;> linarith
      · rintro ⟨h1, h2⟩; constructor <;> linarith
    · have hu1 := Int.floor_le (-c + Real.sqrt (y / α))
      have hu2 := Int.lt_floor_add_one (-c + Real.sqrt (y / α))
      have hv1 := Int.le_ceil (-c - Real.sqrt (y / α))
      have hv2 := Int.ceil_lt_add_one (-c - Real.sqrt (y / α))
      have hR := Real.sqrt_nonneg (y / α)
      have hnn : 0 ≤ ⌊-c + Real.sqrt (y / α)⌋ + 1 - ⌈-c - Real.sqrt (y / α)⌉ := by
        have : ⌈-c - Real.sqrt (y / α)⌉ - 1 ≤ ⌊-c + Real.sqrt (y / α)⌋ := by
          apply Int.le_floor.mpr
          push_cast
          linarith
        linarith
      rw [Int.card_Icc]
      have hcast : (((⌊-c + Real.sqrt (y / α)⌋ + 1 - ⌈-c - Real.sqrt (y / α)⌉).toNat : ℕ) : ℝ)
          = (((⌊-c + Real.sqrt (y / α)⌋ + 1 - ⌈-c - Real.sqrt (y / α)⌉ : ℤ)) : ℝ) := by
        exact_mod_cast Int.toNat_of_nonneg hnn
      rw [hcast]
      push_cast
      rw [abs_le]
      constructor <;> linarith

theorem qForm_count : ∀ α γ l θ₁ θ₂ x : ℝ, 1 ≤ α → 1 ≤ γ → 1 ≤ x →
    {v : ℤ × ℤ | qForm α γ l θ₁ θ₂ v ≤ x}.Finite ∧
    |(({v : ℤ × ℤ | qForm α γ l θ₁ θ₂ v ≤ x}.ncard : ℕ) : ℝ) - Real.pi / Real.sqrt (α * γ) * x|
      ≤ 10 * Real.sqrt x := by
  intro α γ l θ₁ θ₂ x hα hγ hx
  have hα0 : 0 < α := by linarith
  have hγ0 : 0 < γ := by linarith
  have hx0 : 0 < x := by linarith
  choose F hF hFb using fun k : ℤ => row_count α (θ₁ + l * k) (x - γ * (k + θ₂) ^ 2) hα0
  obtain ⟨R, hR⟩ : ∃ R, R = Real.sqrt (x / γ) := ⟨_, rfl⟩
  have hR0 : 0 ≤ R := hR ▸ Real.sqrt_nonneg _
  obtain ⟨k0, hk0⟩ : ∃ k0 : ℤ, k0 = ⌊-θ₂ - R⌋ := ⟨_, rfl⟩
  obtain ⟨n, hn⟩ : ∃ n : ℕ, n = ⌈2 * R⌉₊ + 2 := ⟨_, rfl⟩
  have hk0a : (k0 : ℝ) ≤ -θ₂ - R := by rw [hk0]; exact Int.floor_le _
  have hk0b : -θ₂ - R - 1 < (k0 : ℝ) := by rw [hk0]; exact Int.sub_one_lt_floor _
  have hna : 2 * R + 2 ≤ (n : ℝ) := by
    rw [hn]; push_cast; linarith [Nat.le_ceil (2 * R)]
  have hnb : (n : ℝ) < 2 * R + 3 := by
    rw [hn]; push_cast; linarith [Nat.ceil_lt_add_one (by linarith : (0:ℝ) ≤ 2 * R)]
  have hrow : ∀ k : ℤ, γ * (k + θ₂) ^ 2 ≤ x → ∃ i ∈ Finset.range n, k = k0 + i := by
    intro k hk
    have hk' : ((k : ℝ) + θ₂) ^ 2 ≤ x / γ := by rw [le_div_iff₀ hγ0]; linarith
    rw [Real.sq_le (div_nonneg hx0.le hγ0.le), ← hR] at hk'
    have h1 : k0 ≤ k := by
      have : (k0 : ℝ) ≤ k := by linarith [hk'.1]
      exact_mod_cast this
    have h2 : k < k0 + n := by
      have : (k : ℝ) < k0 + n := by linarith [hk'.2]
      exact_mod_cast this
    refine ⟨(k - k0).toNat, ?_, ?_⟩
    · rw [Finset.mem_range]; omega
    · omega
  have hset : {v : ℤ × ℤ | qForm α γ l θ₁ θ₂ v ≤ x}
      = ↑((Finset.range n).biUnion (fun i : ℕ => (F (k0 + i)).image (fun m => (m, k0 + (i : ℤ))))) := by
    ext ⟨m, k⟩
    simp only [Set.mem_setOf_eq, Finset.coe_biUnion, Finset.coe_image, Set.mem_iUnion,
      Set.mem_image, Finset.mem_coe, Prod.mk.injEq, qForm]
    constructor
    · intro hq
      have hk : γ * ((k : ℝ) + θ₂) ^ 2 ≤ x := by
        have := mul_nonneg hα0.le (sq_nonneg ((m : ℝ) + θ₁ + l * k))
        linarith
      obtain ⟨i, hi, rfl⟩ := hrow k hk
      refine ⟨i, hi, m, ?_, rfl, rfl⟩
      rw [hF]
      push_cast at hq ⊢
      have e : (m : ℝ) + (θ₁ + l * ((k0 : ℝ) + i)) = m + θ₁ + l * ((k0 : ℝ) + i) := by ring
      rw [e]
      linarith
    · rintro ⟨i, hi, m', hm', h1, h2⟩
      subst h1 h2
      rw [hF] at hm'
      push_cast at hm' ⊢
      have e : (m' : ℝ) + (θ₁ + l * ((k0 : ℝ) + i)) = m' + θ₁ + l * ((k0 : ℝ) + i) := by ring
      rw [e] at hm'
      linarith
  refine ⟨hset ▸ Finset.finite_toSet _, ?_⟩
  rw [hset, Set.ncard_coe_finset, Finset.card_biUnion]
  swap
  · intro i _ j _ hij
    change Disjoint _ _
    rw [Finset.disjoint_left]
    intro v hvi hvj
    rw [Finset.mem_image] at hvi hvj
    obtain ⟨a, _, rfl⟩ := hvi
    obtain ⟨b, _, hb⟩ := hvj
    have := congrArg Prod.snd hb
    simp only at this
    exact hij (by exact_mod_cast (add_left_cancel this).symm)
  have hcard : ∀ i ∈ Finset.range n,
      ((F (k0 + i)).image (fun m => (m, k0 + (i : ℤ)))).card = (F (k0 + i)).card :=
    fun i _ => Finset.card_image_of_injective _ (fun a b h => congrArg Prod.fst h)
  rw [Finset.sum_congr rfl hcard]
  push_cast
  have hU := unimodal_sum_integral (fun t => 2 * Real.sqrt ((x - γ * t ^ 2) / α))
    (fun t => by positivity)
    (fun s t hst => by
      apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 2)
      apply Real.sqrt_le_sqrt
      apply div_le_div_of_nonneg_right _ hα0.le
      have := mul_le_mul_of_nonneg_left (sq_le_sq.mpr hst) hγ0.le
      linarith)
    ((k0 : ℝ) + θ₂) n
  have hE := integral_ellipse_width α γ x ((k0 : ℝ) + θ₂) ((k0 : ℝ) + θ₂ + n) hα0 hγ0 hx0
    (by rw [← hR]; linarith) (by rw [← hR]; linarith)
  beta_reduce at hU
  rw [hE] at hU
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, sub_zero] at hU
  have hrowb : ∀ i ∈ Finset.range n, |((F (k0 + i)).card : ℝ)
      - 2 * Real.sqrt ((x - γ * ((k0 : ℝ) + θ₂ + i) ^ 2) / α)| ≤ 1 := by
    intro i _
    have := hFb (k0 + i)
    push_cast at this
    rw [show (k0 : ℝ) + θ₂ + i = k0 + i + θ₂ by ring]
    exact this
  have h1 : |∑ i ∈ Finset.range n, (((F (k0 + i)).card : ℝ)
      - 2 * Real.sqrt ((x - γ * ((k0 : ℝ) + θ₂ + i) ^ 2) / α))| ≤ n :=
    (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum hrowb).trans (by simp))
  have hsx : (1:ℝ) ≤ Real.sqrt x := by
    rw [show (1:ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hx
  have hRx : R ≤ Real.sqrt x := by
    rw [hR]; exact Real.sqrt_le_sqrt (div_le_self hx0.le hγ)
  have hαx : Real.sqrt (x / α) ≤ Real.sqrt x := Real.sqrt_le_sqrt (div_le_self hx0.le hα)
  calc |(∑ i ∈ Finset.range n, ((F (k0 + i)).card : ℝ)) - Real.pi / Real.sqrt (α * γ) * x|
      = |(∑ i ∈ Finset.range n, (((F (k0 + i)).card : ℝ)
          - 2 * Real.sqrt ((x - γ * ((k0 : ℝ) + θ₂ + i) ^ 2) / α)))
        + ((∑ i ∈ Finset.range n, 2 * Real.sqrt ((x - γ * ((k0 : ℝ) + θ₂ + i) ^ 2) / α))
          - Real.pi / Real.sqrt (α * γ) * x)| := by
        rw [Finset.sum_sub_distrib]; congr 1; ring
    _ ≤ _ := abs_add_le _ _
    _ ≤ n + 2 * Real.sqrt (x / α) := add_le_add h1 hU
    _ ≤ 10 * Real.sqrt x := by linarith

end GlobalTheory.Hk
