import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.StatementE
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KurComplete

noncomputable section
open NumberField

namespace Formalism.L2.Th1.GD

open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)

section SlopeTestRemainingChoices

variable {p : ℕ} [hp : Fact p.Prime]

lemma norm_p_eq : ‖(p : ℂ_[p])‖ = (p : ℝ)⁻¹ := by
  have h : ‖(((p : ℚ_[p]) : ℚ_[p]) : ℂ_[p])‖ = ‖(p : ℚ_[p])‖ := PadicComplex.norm_extends' p _
  have h2 : (((p : ℚ_[p]) : ℚ_[p]) : ℂ_[p]) = (p : ℂ_[p]) := by
    simp
  rw [h2] at h
  rw [h]
  exact Padic.norm_p

lemma norm_p_pos : 0 < ‖(p : ℂ_[p])‖ := by
  rw [norm_p_eq]
  have : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  positivity

lemma norm_p_lt_one : ‖(p : ℂ_[p])‖ < 1 := by
  rw [norm_p_eq]
  have : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  exact inv_lt_one_of_one_lt₀ this

lemma norm_le_one_of_isIntegralElem {x : ℂ_[p]} (hx : (Int.castRingHom ℂ_[p]).IsIntegralElem x) :
    ‖x‖ ≤ 1 := by
  obtain ⟨P, hP, hPx⟩ := hx
  have hx' : IsIntegral (NormedField.valuation (K := ℂ_[p])).integer x := by
    refine ⟨P.map (Int.castRingHom _), hP.map _, ?_⟩
    rw [Polynomial.eval₂_map, ← hPx]
    congr 1
  have h := (Valuation.integer.integers (NormedField.valuation (K := ℂ_[p]))).mem_of_integral hx'
  rw [Valuation.mem_integer_iff, NormedField.valuation_apply] at h
  exact_mod_cast h

lemma norm_map_le_one {E : Type} [Field E] [NumberField E] (ψ : E →+* ℂ_[p]) (y : 𝓞 E) :
    ‖ψ (y : E)‖ ≤ 1 := by
  obtain ⟨P, hP, hPx⟩ := RingOfIntegers.isIntegral_coe y
  refine norm_le_one_of_isIntegralElem ⟨P, hP, ?_⟩
  have h := congrArg ψ hPx
  rw [Polynomial.hom_eval₂, map_zero] at h
  rw [← h]
  congr 1
  exact Subsingleton.elim _ _

lemma kur_step {a : ℂ_[p]} (ha : a ∈ MaximalUnramifiedExtension p) (m : ℤ) (h : ‖a‖ < ‖(p : ℂ_[p])‖ ^ m) :
    ‖a‖ ≤ ‖(p : ℂ_[p])‖ ^ (m + 1) := by
  by_cases h0 : a = 0
  · rw [h0, norm_zero]
    exact (zpow_pos norm_p_pos _).le
  · obtain ⟨k, hk⟩ := Formalism.L2.Th1.D.kurUnram p a ha h0
    rw [hk] at h ⊢
    have h1 : m < k := (zpow_lt_zpow_iff_right_of_lt_one₀ norm_p_pos norm_p_lt_one).1 h
    exact (zpow_le_zpow_iff_right_of_lt_one₀ norm_p_pos norm_p_lt_one).2 (by omega)

end SlopeTestRemainingChoices

theorem InertiaRam_proof : InertiaRam := by
  intro p _ _ E _ _ s δ φ hδ hsδ hss hK
  set q : ℝ := ‖(p : ℂ_[p])‖ with hq
  have hq0 : 0 < q := norm_p_pos
  have hq1 : q < 1 := norm_p_lt_one
  set d : ℝ := ‖φ δ‖ with hd
  have hd0 : 0 ≤ d := norm_nonneg _
  have hdq : d ^ 2 = q := by
    rw [hd, ← norm_pow, ← map_pow, hδ, map_neg, map_natCast, norm_neg]
  have hdpos : 0 < d := by
    rcases hd0.lt_or_eq with h | h
    · exact h
    · rw [← h] at hdq
      norm_num at hdq
      exact absurd hdq hq0.ne
  have hd1 : d < 1 := by
    by_contra h
    rw [not_lt] at h
    have : 1 ≤ d ^ 2 := one_le_pow₀ h
    linarith
  have hqd : q ≤ d := by
    rw [← hdq]
    nlinarith
  have hδ0 : δ ≠ 0 := by
    intro h
    rw [hd, h, map_zero, norm_zero] at hdpos
    exact lt_irrefl _ hdpos
  have hdr : d = q ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow, ← hdq, Real.sqrt_sq hd0]

  have key : ∀ b : ℂ_[p], b ∈ MaximalUnramifiedExtension p → ‖b‖ * d ≤ 1 → ‖b‖ ≤ 1 := by
    intro b hb h
    have h1 : ‖b‖ < q ^ (-1 : ℤ) := by
      rw [zpow_neg_one, ← hdq, ← one_div, lt_div_iff₀ (by positivity)]
      calc ‖b‖ * d ^ 2 = (‖b‖ * d) * d := by ring
        _ ≤ 1 * d := mul_le_mul_of_nonneg_right h hd0
        _ < 1 := by rw [one_mul]; exact hd1
    have := kur_step hb (-1) h1
    simpa using this
  have hint : ∀ y : 𝓞 E, ‖φ (y : E)‖ ≤ 1 := fun y => norm_map_le_one φ y
  have hints : ∀ y : 𝓞 E, ‖φ (s (y : E))‖ ≤ 1 := fun y => norm_map_le_one (φ.comp (s : E →+* E)) y
  refine ⟨hdr, ?_, ?_⟩
  · intro y
    rw [← hdr]
    set w : E := (y : E) - s (y : E) with hw
    have hsw : s (w / δ) = w / δ := by
      rw [map_div₀, hsδ, hw, map_sub, hss, div_neg, ← neg_div, neg_sub]
    have hw1 : ‖φ w‖ ≤ 1 := by
      rw [hw, map_sub, sub_eq_add_neg]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hint y) ?_)
      rw [norm_neg]
      exact hints y
    have hmul : ‖φ (w / δ)‖ * d = ‖φ w‖ := by
      rw [hd, ← norm_mul, ← map_mul, div_mul_cancel₀ _ hδ0]
    have h1 := key _ (hK _ hsw) (by rw [hmul]; exact hw1)
    rw [← map_sub, ← hw, ← hmul]
    exact mul_le_of_le_one_left hd0 h1
  · intro y hy
    set a : E := ((y : E) + s (y : E)) / 2 with ha
    set b : E := ((y : E) - s (y : E)) / (2 * δ) with hb
    have hsa : s a = a := by
      rw [ha, map_div₀, map_add, hss, map_ofNat, add_comm]
    have hsb : s b = b := by
      rw [hb, map_div₀, map_mul, hsδ, map_sub, hss, map_ofNat, mul_neg, div_neg, ← neg_div, neg_sub]
    have hy' : (y : E) = a + b * δ := by
      rw [ha, hb]
      field_simp
      ring
    have hnb : ‖φ (b * δ)‖ = ‖φ b‖ * d := by rw [map_mul, norm_mul]
    by_cases hne : ‖φ a‖ = ‖φ (b * δ)‖
    ·
      by_cases hb0 : φ b = 0
      · have ha0 : φ a = 0 := by
          rw [hnb, hb0, norm_zero, zero_mul] at hne
          exact norm_eq_zero.1 hne
        rw [hy', map_add, map_mul, ha0, hb0, zero_mul, add_zero, norm_zero]
        exact hd0
      · exfalso
        have ha0 : φ a ≠ 0 := by
          intro h
          rw [hnb, h, norm_zero] at hne
          have : 0 < ‖φ b‖ * d := mul_pos (norm_pos_iff.2 hb0) hdpos
          linarith
        obtain ⟨k, hk⟩ := Formalism.L2.Th1.D.kurUnram p _ (hK _ hsa) ha0
        obtain ⟨m, hm⟩ := Formalism.L2.Th1.D.kurUnram p _ (hK _ hsb) hb0
        have h2 : (‖φ a‖) ^ 2 = (‖φ b‖) ^ 2 * q := by
          rw [hne, hnb, mul_pow, hdq]
        rw [hk, hm, ← hq] at h2
        have h3 : q ^ (2 * k) = q ^ (2 * m + 1) := by
          rw [zpow_add₀ hq0.ne', zpow_one, mul_comm 2 k, mul_comm 2 m, zpow_mul, zpow_mul]
          exact_mod_cast h2
        have h4 := zpow_right_injective₀ hq0 hq1.ne h3
        omega
    · have hmax : ‖φ (y : E)‖ = max ‖φ a‖ ‖φ (b * δ)‖ := by
        rw [hy', map_add]
        exact IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne
      rw [hmax] at hy ⊢
      have hA : ‖φ a‖ < 1 := (le_max_left _ _).trans_lt hy
      have hB : ‖φ (b * δ)‖ < 1 := (le_max_right _ _).trans_lt hy
      refine max_le ?_ ?_
      · have := kur_step (hK _ hsa) 0 (by simpa using hA)
        rw [zero_add, zpow_one] at this
        exact this.trans hqd
      · rw [hnb] at hB ⊢
        exact mul_le_of_le_one_left hd0 (key _ (hK _ hsb) hB.le)

end Formalism.L2.Th1.GD
