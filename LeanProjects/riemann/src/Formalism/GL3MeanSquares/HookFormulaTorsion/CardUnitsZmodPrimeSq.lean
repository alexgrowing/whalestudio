import Mathlib
import Formalism.GL3MeanSquares.RankMulPowThreeHalvesLeFourthPower

namespace Formalism.HermitianLattices.GenusMassVolumes

open Finset MeasureTheory

theorem hecke_spectral_gap : SW_hecke_gap := by
  intro q M hq hM
  have hq0 : (0 : ℝ) < q := by linarith
  have h1 : q ^ 3 ≤ q ^ M := pow_le_pow_right₀ (by linarith) hM
  have h2 : 0 < q ^ (2 - (M : ℤ)) := zpow_pos hq0 _
  have h3 : q ^ 2 + 1 < q ^ 3 := by nlinarith [sq_nonneg q, mul_pos hq0 hq0]
  have hgap : q ^ 2 + q < q ^ M + q - 1 + q ^ (2 - (M : ℤ)) := by linarith
  refine ⟨hgap, ?_⟩
  intro S hS hle
  by_contra hne
  have hSpos : 0 < S := lt_of_le_of_ne hS (Ne.symm hne)
  have := mul_lt_mul_of_pos_right hgap hSpos
  linarith

private lemma card_units_zmod_prime_sq (p : ℕ) (hp : p.Prime) [NeZero (p ^ 2)] :
    (Finset.univ.filter (fun a : ZMod (p ^ 2) => IsUnit a)).card = p * (p - 1) := by
  classical
  have h1 : Finset.univ.filter (fun a : ZMod (p ^ 2) => IsUnit a)
      = (Finset.univ : Finset (ZMod (p ^ 2))ˣ).map ⟨Units.val, Units.val_injective⟩ := by
    ext a
    constructor
    · intro ha
      obtain ⟨u, hu⟩ := (Finset.mem_filter.mp ha).2
      exact Finset.mem_map.mpr ⟨u, Finset.mem_univ _, hu⟩
    · intro ha
      obtain ⟨u, _, hu⟩ := Finset.mem_map.mp ha
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨u, hu⟩⟩
  rw [h1, Finset.card_map, Finset.card_univ, ZMod.card_units_eq_totient,
    Nat.totient_prime_pow hp (by norm_num)]
  simp

theorem hecke_operator_terms : SW_hecke_terms := by
  classical
  intro p hp
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  have hp1 : 1 ≤ p := hp.one_lt.le
  obtain ⟨k, rfl⟩ : ∃ k, p = k + 1 := ⟨p - 1, by omega⟩
  constructor
  · rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, ZMod.card, ZMod.card_units_eq_totient,
      Nat.totient_prime hp]
    simp
    ring
  · rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
      Nat.totient_prime_pow hp (by norm_num), Fintype.card_subtype]
    have hU := card_units_zmod_prime_sq (k + 1) hp
    have hN : (Finset.univ.filter (fun a : ZMod ((k + 1) ^ 2) => ¬ IsUnit a)).card = k + 1 := by
      have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (ZMod ((k + 1) ^ 2))))
        (fun a => IsUnit a)
      rw [hU, Finset.card_univ, ZMod.card] at this
      simp at this
      nlinarith
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (ZMod ((k + 1) ^ 2) × ZMod ((k + 1) ^ 2))))
      (fun v => IsUnit v.1 ∨ IsUnit v.2)
    have hcompl : (Finset.univ.filter
        (fun v : ZMod ((k + 1) ^ 2) × ZMod ((k + 1) ^ 2) => ¬ (IsUnit v.1 ∨ IsUnit v.2)))
        = (Finset.univ.filter (fun a : ZMod ((k + 1) ^ 2) => ¬ IsUnit a)) ×ˢ
          (Finset.univ.filter (fun a : ZMod ((k + 1) ^ 2) => ¬ IsUnit a)) := by
      ext v
      simp [not_or]
    rw [hcompl, Finset.card_product, hN, Finset.card_univ, Fintype.card_prod, ZMod.card] at hsplit
    simp
    nlinarith

theorem height_integral_formula : SW_height_integral := by
  intro M f c R hM hc hR
  obtain ⟨k, rfl⟩ : ∃ k, M = k + 3 := ⟨M - 3, by omega⟩
  have hA : 0 < c * R ^ (2 * f) := by positivity
  have hcongr : ∫ t in (0 : ℝ)..(c * R ^ (2 * f)), (R ^ (2 * f) / t) * t ^ (k + 3 - 1) / t
      = ∫ t in (0 : ℝ)..(c * R ^ (2 * f)), R ^ (2 * f) * t ^ k := by
    apply intervalIntegral.integral_congr_ae
    refine Filter.Eventually.of_forall ?_
    intro t ht
    rw [Set.uIoc_of_le hA.le] at ht
    have ht0 : t ≠ 0 := ht.1.ne'
    have : k + 3 - 1 = k + 2 := by omega
    rw [this]
    field_simp
    ring
  rw [hcongr, intervalIntegral.integral_const_mul, integral_pow]
  have e1 : k + 3 - 2 = k + 1 := by omega
  have e2 : 2 * f * (k + 3 - 1) = 2 * f + 2 * f * (k + 1) := by
    have : k + 3 - 1 = 1 + (k + 1) := by omega
    rw [this]; ring
  rw [e1, e2, pow_add R, pow_mul R (2 * f) (k + 1), mul_pow]
  have hk : ((k : ℝ) + 1) ≠ 0 := by positivity
  have hk' : (((k + 3 : ℕ) : ℝ) - 2) = (k : ℝ) + 1 := by push_cast; ring
  rw [hk']
  simp only [ne_eq, Nat.add_eq_zero_iff, one_ne_zero, and_false, not_false_eq_true, zero_pow, sub_zero]
  field_simp

theorem real_gaussian_integral : SW_real_gaussian := by
  intro M τ b hτ
  have hne : τ + 2 * (b : ℂ) ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp at this
    linarith
  set β : ℂ := -(Real.pi * Complex.I * (τ + 2 * (b : ℂ))) with hβ
  have hre : 0 < β.re := by
    simp [hβ]
    exact mul_pos Real.pi_pos hτ
  have hint := GaussianFourier.integral_cexp_neg_mul_sq_norm
    (V := EuclideanSpace ℝ (Fin (2 * M))) hre
  have hcongr : (∫ x : EuclideanSpace ℝ (Fin (2 * M)),
        Complex.exp (Real.pi * Complex.I * τ * ((‖x‖ ^ 2 : ℝ) : ℂ)
          + 2 * Real.pi * Complex.I * b * ((‖x‖ ^ 2 : ℝ) : ℂ)))
      = ∫ x : EuclideanSpace ℝ (Fin (2 * M)), Complex.exp (-β * (‖x‖ : ℂ) ^ 2) := by
    congr 1
    ext x
    congr 1
    rw [hβ]
    push_cast
    ring
  rw [hcongr, hint]
  have hfin : ((Module.finrank ℝ (EuclideanSpace ℝ (Fin (2 * M))) : ℂ) / 2) = (M : ℂ) := by
    simp
  rw [hfin, Complex.cpow_natCast, ← mul_pow]
  congr 1
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [hβ]
  field_simp
  ring_nf
  simp

theorem real_place_decay : SW_real_decay := by
  intro M b
  rw [norm_pow]
  apply pow_le_pow_left₀ (norm_nonneg _)
  have hmax : (0 : ℝ) < max 1 |b| := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hz : 2 * max 1 |b| ≤ ‖2 * Complex.I + 2 * (b : ℂ)‖ := by
    have h1 := Complex.abs_im_le_norm (2 * Complex.I + 2 * (b : ℂ))
    have h2 := Complex.abs_re_le_norm (2 * Complex.I + 2 * (b : ℂ))
    simp at h1 h2
    rcases max_cases 1 |b| with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> linarith
  rw [norm_div]
  have h2 : ‖(2 * Complex.I : ℂ)‖ = 2 := by simp
  rw [h2, div_le_iff₀ (lt_of_lt_of_le (by positivity) hz)]
  calc (2 : ℝ) = (max 1 |b|)⁻¹ * (2 * max 1 |b|) := by field_simp
    _ ≤ (max 1 |b|)⁻¹ * ‖2 * Complex.I + 2 * (b : ℂ)‖ :=
      mul_le_mul_of_nonneg_left hz (inv_nonneg.mpr hmax.le)

end Formalism.HermitianLattices.GenusMassVolumes
