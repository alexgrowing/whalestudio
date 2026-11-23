import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.SelfDualStd

noncomputable section
open scoped ComplexConjugate

namespace PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS

section IsKsec
variable (b : ℤ) (d : ℕ)

def IsK (t : ℂ) : Prop := ∃ p q r : ℤ, r ≠ 0 ∧ (r : ℂ) * t = p + q * cmTheta b d

variable {b d}

lemma isK_int (n : ℤ) : IsK b d n := by
  unfold PI.UnitaryGroupMassFormula.UnimodLocStd.IsK
  exact ⟨n, 0, 1, one_ne_zero, by simp⟩

lemma isK_theta : IsK b d (cmTheta b d) := by
  unfold PI.UnitaryGroupMassFormula.UnimodLocStd.IsK
  exact ⟨0, 1, 1, one_ne_zero, by simp⟩

lemma isK_add {t t' : ℂ} (h : IsK b d t) (h' : IsK b d t') : IsK b d (t + t') := by
  obtain ⟨p, q, r, hr, h⟩ := h
  obtain ⟨p', q', r', hr', h'⟩ := h'
  unfold PI.UnitaryGroupMassFormula.UnimodLocStd.IsK
  refine ⟨r' * p + r * p', r' * q + r * q', r * r', mul_ne_zero hr hr', ?_⟩
  push_cast
  linear_combination (r' : ℂ) * h + (r : ℂ) * h'

lemma isK_neg {t : ℂ} (h : IsK b d t) : IsK b d (-t) := by
  obtain ⟨p, q, r, hr, h⟩ := h
  unfold PI.UnitaryGroupMassFormula.UnimodLocStd.IsK
  refine ⟨-p, -q, r, hr, ?_⟩
  push_cast
  linear_combination -h

lemma isK_sub {t t' : ℂ} (h : IsK b d t) (h' : IsK b d t') : IsK b d (t - t') := by
  rw [sub_eq_add_neg]
  exact PI.UnitaryGroupMassFormula.UnimodLocStd.isK_add h (PI.UnitaryGroupMassFormula.UnimodLocStd.isK_neg h')

private lemma conj_cmTheta : conj (cmTheta b d) = (b : ℂ) - cmTheta b d := by
  unfold cmTheta
  simp only [map_div₀, map_add, map_mul, Complex.conj_I, Complex.conj_ofReal, map_intCast, map_ofNat]
  ring

lemma isK_conj {t : ℂ} (h : IsK b d t) : IsK b d (conj t) := by
  obtain ⟨p, q, r, hr, h⟩ := h
  have h2 : (r : ℂ) * conj t = p + q * conj (cmTheta b d) := by
    have h3 := congrArg conj h
    simpa using h3
  unfold PI.UnitaryGroupMassFormula.UnimodLocStd.IsK
  refine ⟨p + q * b, -q, r, hr, ?_⟩
  rw [h2, PI.UnitaryGroupMassFormula.UnimodLocStd.conj_cmTheta]
  push_cast
  ring

variable {e : ℤ} (hn : cmTheta b d * (b - cmTheta b d) = (e : ℂ))
include hn

lemma isK_mul {t t' : ℂ} (h : IsK b d t) (h' : IsK b d t') : IsK b d (t * t') := by
  obtain ⟨p, q, r, hr, h⟩ := h
  obtain ⟨p', q', r', hr', h'⟩ := h'
  unfold PI.UnitaryGroupMassFormula.UnimodLocStd.IsK
  refine ⟨p * p' - q * q' * e, p * q' + q * p' + q * q' * b, r * r', mul_ne_zero hr hr', ?_⟩
  push_cast
  linear_combination ((r' : ℂ) * t') * h + ((p : ℂ) + q * cmTheta b d) * h' - ((q : ℂ) * q') * hn

lemma isK_inv {t : ℂ} (h : IsK b d t) : IsK b d t⁻¹ := by
  by_cases ht : t = 0
  · rw [ht, inv_zero]
    simpa using PI.UnitaryGroupMassFormula.UnimodLocStd.isK_int (b := b) (d := d) 0
  obtain ⟨p, q, r, hr, h⟩ := h
  have hrt : (r : ℂ) * t ≠ 0 := mul_ne_zero (Int.cast_ne_zero.mpr hr) ht

  have hz : ((p ^ 2 + p * q * b + q ^ 2 * e : ℤ) : ℂ) =
      (r : ℂ) * t * (p + q * b - q * cmTheta b d) := by
    rw [h]
    push_cast
    linear_combination (-(q : ℂ) ^ 2) * hn
  unfold PI.UnitaryGroupMassFormula.UnimodLocStd.IsK
  by_cases hN : p ^ 2 + p * q * b + q ^ 2 * e = 0
  ·
    have hw : (p : ℂ) + q * b - q * cmTheta b d = 0 := by
      have h0 : (r : ℂ) * t * (p + q * b - q * cmTheta b d) = 0 := by
        rw [← hz, hN, Int.cast_zero]
      exact (mul_eq_zero.mp h0).resolve_left hrt
    have hk : (r : ℂ) * t = ((2 * p + q * b : ℤ) : ℂ) := by
      rw [h]
      push_cast
      linear_combination -hw
    have hk0 : (2 * p + q * b : ℤ) ≠ 0 := by
      intro h0
      rw [h0, Int.cast_zero] at hk
      exact hrt hk
    refine ⟨r, 0, 2 * p + q * b, hk0, ?_⟩
    rw [← hk, mul_inv_cancel_right₀ ht]
    simp
  · refine ⟨r * (p + q * b), -(r * q), p ^ 2 + p * q * b + q ^ 2 * e, hN, ?_⟩
    rw [hz]
    field_simp
    push_cast
    ring

lemma isK_sum {ι : Type*} (s : Finset ι) (f : ι → ℂ) (hf : ∀ i ∈ s, IsK b d (f i)) : IsK b d (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using PI.UnitaryGroupMassFormula.UnimodLocStd.isK_int (b := b) (d := d) 0
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact PI.UnitaryGroupMassFormula.UnimodLocStd.isK_add (hf a (Finset.mem_insert_self a s))
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

end IsKsec

end PI.UnitaryGroupMassFormula.UnimodLocStd
