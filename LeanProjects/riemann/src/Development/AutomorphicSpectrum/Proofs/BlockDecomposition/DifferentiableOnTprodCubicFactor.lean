import Mathlib

namespace GlobalTheory.CompanionTheory.EulerThree

noncomputable def cubicFactor (p : ℕ) (a b c s : ℂ) : ℂ :=
  (1 - a * (p : ℂ) ^ (-s))⁻¹ * (1 - b * (p : ℂ) ^ (-s))⁻¹ * (1 - c * (p : ℂ) ^ (-s))⁻¹

theorem norm_param_mul {p : ℕ} (hp : 2 ≤ p) {a : ℂ} (ha : ‖a‖ = 1) (s : ℂ) :
    ‖a * (p : ℂ) ^ (-s)‖ = (p : ℝ) ^ (-s.re) := by
  rw [norm_mul, ha, one_mul, Complex.norm_natCast_cpow_of_pos (by omega)]
  simp

theorem rpow_neg_le_half {p : ℕ} (hp : 2 ≤ p) {σ : ℝ} (hσ : 1 ≤ σ) :
    (p : ℝ) ^ (-σ) ≤ 1 / 2 := by
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have h1 : (p : ℝ) ^ (-σ) ≤ (p : ℝ) ^ (-1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have h2 : (p : ℝ) ^ (-1 : ℝ) ≤ 1 / 2 := by
    rw [Real.rpow_neg_one, one_div]
    exact inv_anti₀ (by norm_num) hp'
  exact h1.trans h2

theorem one_sub_ne_zero_of_le {x : ℂ} (hx : ‖x‖ ≤ 1 / 2) : 1 - x ≠ 0 := by
  intro h
  have : x = 1 := (sub_eq_zero.1 h).symm
  rw [this, norm_one] at hx
  norm_num at hx

theorem norm_inv_one_sub_sub_one_le {x : ℂ} (hx : ‖x‖ ≤ 1 / 2) :
    ‖(1 - x)⁻¹ - 1‖ ≤ 2 * ‖x‖ := by
  have hne := one_sub_ne_zero_of_le hx
  have hlow : 1 / 2 ≤ ‖1 - x‖ := by
    have := norm_sub_norm_le (1 : ℂ) x
    rw [norm_one] at this
    linarith
  have e : (1 - x)⁻¹ - 1 = x * (1 - x)⁻¹ := by
    field_simp
    ring
  rw [e, norm_mul, norm_inv]
  have hinv : ‖1 - x‖⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]
    linarith
  nlinarith [norm_nonneg x]

theorem norm_three_sub_one_le {y₁ y₂ y₃ : ℂ} {t : ℝ} (ht : t ≤ 1 / 2)
    (h₁ : ‖y₁‖ ≤ 2 * t) (h₂ : ‖y₂‖ ≤ 2 * t) (h₃ : ‖y₃‖ ≤ 2 * t) :
    ‖(1 + y₁) * (1 + y₂) * (1 + y₃) - 1‖ ≤ 14 * t := by
  have ht0 : 0 ≤ t := by nlinarith [norm_nonneg y₁]
  have e : (1 + y₁) * (1 + y₂) * (1 + y₃) - 1 =
      y₁ + y₂ + y₃ + y₁ * y₂ + y₁ * y₃ + y₂ * y₃ + y₁ * y₂ * y₃ := by ring
  have m₁₂ : ‖y₁ * y₂‖ ≤ 2 * t := by
    rw [norm_mul]
    nlinarith [norm_nonneg y₁, norm_nonneg y₂]
  have m₁₃ : ‖y₁ * y₃‖ ≤ 2 * t := by
    rw [norm_mul]
    nlinarith [norm_nonneg y₁, norm_nonneg y₃]
  have m₂₃ : ‖y₂ * y₃‖ ≤ 2 * t := by
    rw [norm_mul]
    nlinarith [norm_nonneg y₂, norm_nonneg y₃]
  have m₁₂₃ : ‖y₁ * y₂ * y₃‖ ≤ 2 * t := by
    rw [norm_mul]
    have : ‖y₃‖ ≤ 1 := by linarith
    nlinarith [norm_nonneg (y₁ * y₂), norm_nonneg y₃]
  rw [e]
  calc _ ≤ ‖y₁‖ + ‖y₂‖ + ‖y₃‖ + ‖y₁ * y₂‖ + ‖y₁ * y₃‖ + ‖y₂ * y₃‖ + ‖y₁ * y₂ * y₃‖ := by
        refine (norm_add_le _ _).trans (add_le_add_left ?_ _)
        refine (norm_add_le _ _).trans (add_le_add_left ?_ _)
        refine (norm_add_le _ _).trans (add_le_add_left ?_ _)
        refine (norm_add_le _ _).trans (add_le_add_left ?_ _)
        refine (norm_add_le _ _).trans (add_le_add_left ?_ _)
        exact norm_add_le _ _
    _ ≤ 14 * t := by linarith

theorem norm_cubicFactor_sub_one_le {p : ℕ} (hp : 2 ≤ p) {a b c s : ℂ} (ha : ‖a‖ = 1)
    (hb : ‖b‖ = 1) (hc : ‖c‖ = 1) (hs : 1 ≤ s.re) :
    ‖cubicFactor p a b c s - 1‖ ≤ 14 * (p : ℝ) ^ (-s.re) := by
  have ht := rpow_neg_le_half hp hs
  have key : ∀ {u : ℂ}, ‖u‖ = 1 →
      ‖(1 - u * (p : ℂ) ^ (-s))⁻¹ - 1‖ ≤ 2 * (p : ℝ) ^ (-s.re) := fun hu => by
    have hn := norm_param_mul hp hu s
    have := norm_inv_one_sub_sub_one_le (x := _) (hn.le.trans ht)
    rwa [hn] at this
  have := norm_three_sub_one_le ht (key ha) (key hb) (key hc)
  simpa [cubicFactor] using this

theorem differentiableAt_cubicFactor {p : ℕ} (hp : 2 ≤ p) {a b c s : ℂ} (ha : ‖a‖ = 1)
    (hb : ‖b‖ = 1) (hc : ‖c‖ = 1) (hs : 1 ≤ s.re) :
    DifferentiableAt ℂ (fun z => cubicFactor p a b c z) s := by
  have hp0 : (p : ℂ) ≠ 0 := by
    have : p ≠ 0 := by omega
    exact_mod_cast this
  have hpow : DifferentiableAt ℂ (fun z : ℂ => (p : ℂ) ^ (-z)) s :=
    (differentiableAt_id.neg).const_cpow (Or.inl hp0)
  have key : ∀ {u : ℂ}, ‖u‖ = 1 →
      DifferentiableAt ℂ (fun z : ℂ => (1 - u * (p : ℂ) ^ (-z))⁻¹) s := fun hu => by
    refine ((differentiableAt_const _).sub ((differentiableAt_const _).mul hpow)).inv ?_
    exact one_sub_ne_zero_of_le ((norm_param_mul hp hu s).le.trans (rpow_neg_le_half hp hs))
  exact ((key ha).mul (key hb)).mul (key hc)

variable {ι : Type*} {p : ι → ℕ} {a b c : ι → ℂ}

theorem summable_rpow_neg (hinj : Function.Injective p) {σ : ℝ} (hσ : 1 < σ) :
    Summable fun i => (p i : ℝ) ^ (-σ) :=
  (Real.summable_nat_rpow.2 (by linarith)).comp_injective hinj

theorem multipliable_cubicFactor (hinj : Function.Injective p) (hp : ∀ i, 2 ≤ p i)
    (ha : ∀ i, ‖a i‖ = 1) (hb : ∀ i, ‖b i‖ = 1) (hc : ∀ i, ‖c i‖ = 1) {s : ℂ} (hs : 1 < s.re) :
    Multipliable fun i => cubicFactor (p i) (a i) (b i) (c i) s := by
  have hsum : Summable fun i => cubicFactor (p i) (a i) (b i) (c i) s - 1 :=
    Summable.of_norm_bounded ((summable_rpow_neg hinj hs).mul_left 14)
      fun i => norm_cubicFactor_sub_one_le (hp i) (ha i) (hb i) (hc i) hs.le
  simpa using multipliable_one_add_of_summable hsum.norm

theorem differentiableOn_tprod_cubicFactor (hinj : Function.Injective p) (hp : ∀ i, 2 ≤ p i)
    (ha : ∀ i, ‖a i‖ = 1) (hb : ∀ i, ‖b i‖ = 1) (hc : ∀ i, ‖c i‖ = 1) :
    DifferentiableOn ℂ (fun s => ∏' i, cubicFactor (p i) (a i) (b i) (c i) s)
      {s : ℂ | 1 < s.re} := by
  intro s hs
  have hs : 1 < s.re := hs
  obtain ⟨σ₀, h1, h2⟩ : ∃ σ₀ : ℝ, 1 < σ₀ ∧ σ₀ < s.re := exists_between hs
  let K : Set ℂ := {z | σ₀ < z.re}
  have hK : IsOpen K := isOpen_lt continuous_const Complex.continuous_re
  have hKd : ∀ i, DifferentiableOn ℂ (fun z => cubicFactor (p i) (a i) (b i) (c i) z) K :=
    fun i z hz => (differentiableAt_cubicFactor (hp i) (ha i) (hb i) (hc i)
      (by have : σ₀ < z.re := hz
          linarith)).differentiableWithinAt
  have hprod := ((summable_rpow_neg hinj h1).mul_left 14).hasProdLocallyUniformlyOn_one_add
    (f := fun i z => cubicFactor (p i) (a i) (b i) (c i) z - 1) hK
    (.of_forall fun i z hz => by
      have hz' : σ₀ < z.re := hz
      refine (norm_cubicFactor_sub_one_le (hp i) (ha i) (hb i) (hc i)
        (by linarith)).trans ?_
      refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
      have : (2 : ℝ) ≤ p i := by exact_mod_cast hp i
      exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith))
    (fun i => ((hKd i).sub (differentiableOn_const _)).continuousOn)
  have hd : DifferentiableOn ℂ
      (fun z => ∏' i, (1 + (cubicFactor (p i) (a i) (b i) (c i) z - 1))) K :=
    hprod.differentiableOn (.of_forall fun _ => by
      simpa [Finset.prod_fn] using DifferentiableOn.finsetProd (fun i _ => hKd i)) hK
  have h3 := hd.differentiableAt (hK.mem_nhds h2)
  simp only [add_sub_cancel] at h3
  exact h3.differentiableWithinAt

end GlobalTheory.CompanionTheory.EulerThree
