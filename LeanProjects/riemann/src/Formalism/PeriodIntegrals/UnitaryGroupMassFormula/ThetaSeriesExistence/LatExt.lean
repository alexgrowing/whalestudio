import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ThetaSeriesExistence.ThetaDerivNe
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ThetaSeriesExistence.Development

noncomputable section

open Complex Classical

namespace PI.SSE

lemma qf_add (A ω v z : ℂ) (hA : A ≠ 0) :
    qf A v (z + ω) * qf A ω z =
      cexp (Real.pi * ((starRingEnd ℂ) v * ω - (starRingEnd ℂ) ω * v) / (2 * A)) *
        qf A (ω + v) z := by
  simp only [qf, map_add]
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  field_simp
  ring

lemma qf_neg (A ω z : ℂ) (hA : A ≠ 0) : qf A ω (z + -ω) * qf A (-ω) z = 1 := by
  simp only [qf, map_neg]
  rw [← Complex.exp_add, ← Complex.exp_zero]
  congr 1
  field_simp
  ring

lemma qf_zero (A z : ℂ) : qf A 0 z = 1 := by
  simp [qf]

lemma rel_add (G : ℂ → ℂ) (A ω v s t : ℂ) (hA : A ≠ 0)
    (hω : ∀ z, G (z + ω) = s * (qf A ω z * G z)) (hv : ∀ z, G (z + v) = t * (qf A v z * G z)) :
    ∀ z, G (z + (ω + v)) = s * t *
      cexp (Real.pi * ((starRingEnd ℂ) v * ω - (starRingEnd ℂ) ω * v) / (2 * A)) *
        (qf A (ω + v) z * G z) := by
  intro z
  calc G (z + (ω + v)) = G ((z + ω) + v) := by rw [add_assoc]
    _ = t * (qf A v (z + ω) * (s * (qf A ω z * G z))) := by rw [hv, hω]
    _ = s * t * (qf A v (z + ω) * qf A ω z) * G z := by ring
    _ = _ := by rw [qf_add A ω v z hA]; ring

lemma rel_neg (G : ℂ → ℂ) (A ω s s' : ℂ) (hA : A ≠ 0) (hss : s * s' = 1)
    (hω : ∀ z, G (z + ω) = s * (qf A ω z * G z)) :
    ∀ z, G (z + -ω) = s' * (qf A (-ω) z * G z) := by
  intro z
  have h := hω (z + -ω)
  rw [neg_add_cancel_right] at h
  rw [h, show s' * (qf A (-ω) z * (s * (qf A ω (z + -ω) * G (z + -ω)))) =
      (s * s') * (qf A ω (z + -ω) * qf A (-ω) z) * G (z + -ω) by ring, hss, qf_neg A ω z hA]
  ring

lemma exp_int_pi (k : ℤ) : cexp (k * (Real.pi * I)) = (-1 : ℂ) ^ k := by
  rw [Complex.exp_int_mul, Complex.exp_pi_mul_I]

lemma zsign (a b k c : ℤ) (h : Even (a + b + k - c)) :
    (-1 : ℂ) ^ a * (-1 : ℂ) ^ b * (-1 : ℂ) ^ k = (-1 : ℂ) ^ c := by
  have h1 : (-1 : ℂ) ≠ 0 := by norm_num
  rw [← zpow_add₀ h1, ← zpow_add₀ h1, show a + b + k = c + (a + b + k - c) by ring, zpow_add₀ h1,
    h.neg_one_zpow, mul_one]

def Rel (G : ℂ → ℂ) (A v₁ v₂ : ℂ) (m n : ℤ) : Prop :=
  ∀ z, G (z + (m * v₁ + n * v₂)) = (-1 : ℂ) ^ (m + n + m * n) * (qf A (m * v₁ + n * v₂) z * G z)

lemma rel_comb (G : ℂ → ℂ) (A v₁ v₂ : ℂ) (hA : A ≠ 0)
    (hI : (starRingEnd ℂ) v₁ * v₂ - v₁ * (starRingEnd ℂ) v₂ = 2 * I * A) (m n c d : ℤ)
    (h : Rel G A v₁ v₂ m n) (h' : Rel G A v₁ v₂ c d) : Rel G A v₁ v₂ (m + c) (n + d) := by
  unfold Rel at h h' ⊢
  intro z
  have key := rel_add G A ((m : ℂ) * v₁ + n * v₂) ((c : ℂ) * v₁ + d * v₂) _ _ hA h h' z
  have hsum : (m : ℂ) * v₁ + n * v₂ + ((c : ℂ) * v₁ + d * v₂) = ((m + c : ℤ) : ℂ) * v₁ + ((n + d : ℤ) : ℂ) * v₂ := by
    push_cast; ring
  have hdiff : (starRingEnd ℂ) ((c : ℂ) * v₁ + d * v₂) * ((m : ℂ) * v₁ + n * v₂) -
      (starRingEnd ℂ) ((m : ℂ) * v₁ + n * v₂) * ((c : ℂ) * v₁ + d * v₂) =
      ((c * n - m * d : ℤ) : ℂ) * ((starRingEnd ℂ) v₁ * v₂ - v₁ * (starRingEnd ℂ) v₂) := by
    simp only [map_add, map_mul, map_intCast]
    push_cast
    ring
  have hexp : cexp (Real.pi * ((starRingEnd ℂ) ((c : ℂ) * v₁ + d * v₂) * ((m : ℂ) * v₁ + n * v₂) -
      (starRingEnd ℂ) ((m : ℂ) * v₁ + n * v₂) * ((c : ℂ) * v₁ + d * v₂)) / (2 * A)) =
      (-1 : ℂ) ^ (c * n - m * d) := by
    rw [← exp_int_pi, hdiff, hI]
    congr 1
    field_simp
  rw [← hsum, key, hexp, zsign (m + n + m * n) (c + d + c * d) (c * n - m * d) (m + c + (n + d) + (m + c) * (n + d))
    ⟨-(m * d), by ring⟩]

lemma indep (v₁ v₂ : ℂ) (h : ((starRingEnd ℂ) v₁ * v₂).im ≠ 0) (p q : ℤ)
    (hpq : (p : ℂ) * v₁ + q * v₂ = 0) : p = 0 ∧ q = 0 := by
  have hv₁ : v₁ ≠ 0 := by
    rintro rfl
    simp at h
  have him : ((starRingEnd ℂ) v₁ * ((p : ℂ) * v₁ + q * v₂)).im = q * ((starRingEnd ℂ) v₁ * v₂).im := by
    simp [Complex.mul_im, Complex.mul_re]
    ring
  rw [hpq, mul_zero, Complex.zero_im] at him
  have hq : (q : ℝ) = 0 := by
    rcases mul_eq_zero.mp him.symm with h' | h'
    · exact h'
    · exact absurd h' h
  have hq' : q = 0 := by exact_mod_cast hq
  subst hq'
  simp only [Int.cast_zero, zero_mul, add_zero, mul_eq_zero] at hpq
  rcases hpq with hp | hp
  · exact ⟨by exact_mod_cast hp, rfl⟩
  · exact absurd hp hv₁

lemma psi_eq (v₁ v₂ : ℂ) (h : ((starRingEnd ℂ) v₁ * v₂).im ≠ 0) (m n : ℤ) :
    (-1 : ℂ) ^ (m + n + m * n) =
      if ((m : ℂ) * v₁ + n * v₂) / 2 ∈ PI.lat2 v₁ v₂ then 1 else -1 := by
  by_cases hmem : ((m : ℂ) * v₁ + n * v₂) / 2 ∈ PI.lat2 v₁ v₂
  · rw [if_pos hmem]
    unfold PI.lat2 at hmem
    obtain ⟨p, q, hpq⟩ := AddSubgroup.mem_closure_pair.mp hmem
    rw [zsmul_eq_mul, zsmul_eq_mul] at hpq
    obtain ⟨h1, h2⟩ := indep v₁ v₂ h (m - 2 * p) (n - 2 * q) (by push_cast; linear_combination (-2 : ℂ) * hpq)
    obtain rfl : m = 2 * p := by omega
    obtain rfl : n = 2 * q := by omega
    exact Even.neg_one_zpow ⟨p + q + 2 * p * q, by ring⟩
  · rw [if_neg hmem]
    have hodd : Odd (m + n + m * n) := by
      rcases Int.even_or_odd m with ⟨a, ha⟩ | ⟨a, ha⟩ <;> rcases Int.even_or_odd n with ⟨b, hb⟩ | ⟨b, hb⟩
      · exfalso
        apply hmem
        unfold PI.lat2
        refine AddSubgroup.mem_closure_pair.mpr ⟨a, b, ?_⟩
        rw [zsmul_eq_mul, zsmul_eq_mul, ha, hb]
        push_cast
        ring
      · exact ⟨2 * a + b + 2 * a * b, by rw [ha, hb]; ring⟩
      · exact ⟨a + 2 * b + 2 * a * b, by rw [ha, hb]; ring⟩
      · exact ⟨2 * a + 2 * b + 2 * a * b + 1, by rw [ha, hb]; ring⟩
    exact hodd.neg_one_zpow

theorem latExt : LatExt := by
  intro v₁ v₂ hpos G h₁ h₂ ω hω z
  have hne : ((starRingEnd ℂ) v₁ * v₂).im ≠ 0 := hpos.ne'
  have hA : ((((starRingEnd ℂ) v₁ * v₂).im : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hne
  have hI : (starRingEnd ℂ) v₁ * v₂ - v₁ * (starRingEnd ℂ) v₂ =
      2 * I * ((((starRingEnd ℂ) v₁ * v₂).im : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring
  set A : ℂ := ((((starRingEnd ℂ) v₁ * v₂).im : ℝ) : ℂ) with hAdef
  have r10 : Rel G A v₁ v₂ 1 0 := by
    intro z
    have e : ((1 : ℤ) : ℂ) * v₁ + ((0 : ℤ) : ℂ) * v₂ = v₁ := by push_cast; ring
    rw [e, h₁ z]
    norm_num
  have r01 : Rel G A v₁ v₂ 0 1 := by
    intro z
    have e : ((0 : ℤ) : ℂ) * v₁ + ((1 : ℤ) : ℂ) * v₂ = v₂ := by push_cast; ring
    rw [e, h₂ z]
    norm_num
  have r00 : Rel G A v₁ v₂ 0 0 := by
    intro z
    simp [qf_zero]
  have rm10 : Rel G A v₁ v₂ (-1) 0 := by
    intro z
    have hn := rel_neg G A v₁ (-1) (-1) hA (by norm_num) (fun z => by rw [h₁ z]; ring) z
    have e : ((-1 : ℤ) : ℂ) * v₁ + ((0 : ℤ) : ℂ) * v₂ = -v₁ := by push_cast; ring
    rw [e, hn]
    norm_num
  have r0m1 : Rel G A v₁ v₂ 0 (-1) := by
    intro z
    have hn := rel_neg G A v₂ (-1) (-1) hA (by norm_num) (fun z => by rw [h₂ z]; ring) z
    have e : ((0 : ℤ) : ℂ) * v₁ + ((-1 : ℤ) : ℂ) * v₂ = -v₂ := by push_cast; ring
    rw [e, hn]
    norm_num
  have hcol : ∀ m : ℤ, Rel G A v₁ v₂ m 0 := by
    intro m
    refine Int.induction_on m r00 (fun i hi => ?_) (fun i hi => ?_)
    · have h := rel_comb G A v₁ v₂ hA hI _ _ _ _ hi r10
      convert h using 2 <;> omega
    · have h := rel_comb G A v₁ v₂ hA hI _ _ _ _ hi rm10
      convert h using 2 <;> omega
  have hall : ∀ m n : ℤ, Rel G A v₁ v₂ m n := by
    intro m n
    refine Int.induction_on n (hcol m) (fun i hi => ?_) (fun i hi => ?_)
    · have h := rel_comb G A v₁ v₂ hA hI _ _ _ _ hi r01
      convert h using 2 <;> omega
    · have h := rel_comb G A v₁ v₂ hA hI _ _ _ _ hi r0m1
      convert h using 2 <;> omega
  have hω' := hω
  unfold PI.lat2 at hω'
  obtain ⟨m, n, rfl⟩ := AddSubgroup.mem_closure_pair.mp hω'
  have e : m • v₁ + n • v₂ = (m : ℂ) * v₁ + n * v₂ := by rw [zsmul_eq_mul, zsmul_eq_mul]
  rw [e, ← psi_eq v₁ v₂ hne m n]
  exact hall m n z

end PI.SSE

end
