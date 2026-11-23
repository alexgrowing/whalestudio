import Mathlib
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

namespace MonomialMap

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

omit [Fintype ι] [DecidableEq ι] in
theorem evalCone_mul (z : Cone n ℂ) (f g : MvPolynomial (Coord n) ℤ) :
    evalCone z (f * g) = evalCone z f * evalCone z g := by
  simp [evalCone, eval₂_mul]

omit [Fintype ι] [DecidableEq ι] in
theorem evalCone_pow (z : Cone n ℂ) (f : MvPolynomial (Coord n) ℤ) (m : ℕ) :
    evalCone z (f ^ m) = evalCone z f ^ m := by
  simp [evalCone, eval₂_pow]

omit [DecidableEq ι] in

theorem evalCone_chartMonomial_ne_zero (z : Cone n ℂ) (c : (k : ι) → Fin (n k + 1)) (d : ι → ℕ)
    (hc : ∀ k, z k (c k) ≠ 0) : evalCone z (chartMonomial c d) ≠ 0 := by
  simp only [chartMonomial, evalCone, eval₂_prod, eval₂_pow, eval₂_X]
  exact Finset.prod_ne_zero_iff.mpr fun k _ ↦ pow_ne_zero _ (hc k)

omit [Fintype ι] in

theorem live_of_point {P : ArithVariety n} {z : Cone n ℂ} (hz : z ∈ P.points ℂ)
    {c : (k : ι) → Fin (n k + 1)} (hc : ∀ k, z k (c k) ≠ 0) :
    ∀ k, (X ⟨k, c k⟩ : MvPolynomial (Coord n) ℤ) ∉ P.ideal := fun k hk ↦
  hc k (by simpa [evalCone] using hz.2 _ hk)

theorem chart_value_eq {P : ArithVariety n} {num den e e' : MvPolynomial (Coord n) ℤ}
    {c : (k : ι) → Fin (n k + 1)} {d d' : ι → ℕ} (hden : den ∉ P.ideal)
    (h₁ : den * e - num * chartMonomial c d ∈ P.ideal)
    (h₂ : den * e' - num * chartMonomial c d' ∈ P.ideal) {z : Cone n ℂ} (hz : z ∈ P.points ℂ) :
    evalCone z e * evalCone z (chartMonomial c d') =
      evalCone z e' * evalCone z (chartMonomial c d) := by
  have hmem : den * (e * chartMonomial c d' - e' * chartMonomial c d) ∈ P.ideal := by
    have hid : den * (e * chartMonomial c d' - e' * chartMonomial c d) =
        (den * e - num * chartMonomial c d) * chartMonomial c d' -
          (den * e' - num * chartMonomial c d') * chartMonomial c d := by ring
    rw [hid]
    exact P.ideal.sub_mem (P.ideal.mul_mem_right _ h₁) (P.ideal.mul_mem_right _ h₂)
  have h := hz.2 _ ((P.isPrime.mem_or_mem hmem).resolve_left hden)
  simp only [evalCone, eval₂_sub, eval₂_mul] at h
  exact sub_eq_zero.mp h

theorem ratio_norm_eq {e e' x x' : ℂ} (hx : x ≠ 0) (hx' : x' ≠ 0) (h : e * x' = e' * x) (M : ℝ) :
    ‖e‖ / (‖x‖ * M) = ‖e'‖ / (‖x'‖ * M) := by
  rw [← div_div, ← div_div, ← norm_div, ← norm_div, (div_eq_div_iff hx hx').mpr h]

variable {P : ArithVariety n}

theorem supNormLE_mul (A B : HermLine n) (s : IntegralSection P A.deg) (t : IntegralSection P B.deg)
    {C C' : ℝ} (hs : s.SupNormLE A C) (ht : t.SupNormLE B C') :
    IntegralSection.SupNormLE (A.mul B) (s.mul t) (C + C') := by
  intro z hz c d e he hc
  have live := live_of_point hz hc
  obtain ⟨d₁, e₁, he₁⟩ := s.regular c live
  obtain ⟨d₂, e₂, he₂⟩ := t.regular c live
  have hmem : s.den * t.den * (e₁ * e₂) - s.num * t.num * chartMonomial c (d₁ + d₂) ∈ P.ideal := by
    rw [chartMonomial_add]
    have hid : s.den * t.den * (e₁ * e₂) - s.num * t.num * (chartMonomial c d₁ * chartMonomial c d₂) =
        (s.den * e₁ - s.num * chartMonomial c d₁) * (t.den * e₂) +
          (s.num * chartMonomial c d₁) * (t.den * e₂ - t.num * chartMonomial c d₂) := by ring
    rw [hid]
    exact P.ideal.add_mem (P.ideal.mul_mem_right _ he₁.2) (P.ideal.mul_mem_left _ he₂.2)
  have hv := chart_value_eq (s.mul t).den_not_mem he.2 hmem hz
  have hA := hs z hz c d₁ e₁ he₁ hc
  have hB := ht z hz c d₂ e₂ he₂ hc
  change ‖evalCone z e‖ / (‖evalCone z (chartMonomial c d)‖ * (A.metric z * B.metric z)) ≤ _
  rw [ratio_norm_eq (evalCone_chartMonomial_ne_zero z c d hc)
    (evalCone_chartMonomial_ne_zero z c _ hc) hv, evalCone_mul, chartMonomial_add, evalCone_mul,
    norm_mul, norm_mul, Real.exp_add]
  have hid : ‖evalCone z e₁‖ * ‖evalCone z e₂‖ /
      (‖evalCone z (chartMonomial c d₁)‖ * ‖evalCone z (chartMonomial c d₂)‖ * (A.metric z * B.metric z)) =
      (‖evalCone z e₁‖ / (‖evalCone z (chartMonomial c d₁)‖ * A.metric z)) *
        (‖evalCone z e₂‖ / (‖evalCone z (chartMonomial c d₂)‖ * B.metric z)) := by
    rw [div_mul_div_comm]; ring_nf
  rw [hid]
  exact mul_le_mul hA hB
    (div_nonneg (norm_nonneg _) (mul_nonneg (norm_nonneg _) (B.metric_pos z hz.1).le))
    (Real.exp_pos _).le

theorem supNormLE_pow (A : HermLine n) (s : IntegralSection P A.deg) {C : ℝ} (hs : s.SupNormLE A C)
    (m : ℕ) : IntegralSection.SupNormLE (A.pow m) (s.pow m) (m * C) := by
  intro z hz c d e he hc
  have live := live_of_point hz hc
  obtain ⟨d₁, e₁, he₁⟩ := s.regular c live
  have hmem : s.den ^ m * e₁ ^ m - s.num ^ m * chartMonomial c (m • d₁) ∈ P.ideal := by
    rw [chartMonomial_nsmul, ← mul_pow, ← mul_pow]
    exact Ideal.mem_of_dvd _ (sub_dvd_pow_sub_pow _ _ m) he₁.2
  have hv := chart_value_eq (s.pow m).den_not_mem he.2 hmem hz
  have hA := hs z hz c d₁ e₁ he₁ hc
  change ‖evalCone z e‖ / (‖evalCone z (chartMonomial c d)‖ * A.metric z ^ m) ≤ _
  rw [ratio_norm_eq (evalCone_chartMonomial_ne_zero z c d hc)
    (evalCone_chartMonomial_ne_zero z c _ hc) hv, evalCone_pow, chartMonomial_nsmul, evalCone_pow,
    norm_pow, norm_pow, ← mul_pow, ← div_pow, mul_comm (m : ℝ) C, Real.exp_mul, Real.rpow_natCast]
  exact pow_le_pow_left₀
    (div_nonneg (norm_nonneg _) (mul_nonneg (norm_nonneg _) (A.metric_pos z hz.1).le)) hA m

theorem supNormLE_cast (A B : HermLine n) (hdeg : A.deg = B.deg) (hmet : ∀ z, A.metric z = B.metric z)
    (s : IntegralSection P A.deg) {C : ℝ} (hs : s.SupNormLE A C) :
    (s.cast hdeg).SupNormLE B C := by
  intro z hz c d e he hc
  have he' : IsChartForm P A.deg s.num s.den c d e := by
    obtain ⟨⟨δ, hδ, hδk⟩, hmem⟩ := he
    exact ⟨⟨δ, hδ, fun k ↦ by rw [hδk k, hdeg]⟩, hmem⟩
  rw [← hmet z]
  exact hs z hz c d e he' hc

theorem toFun_mul {a b : ι → ℤ} (s : IntegralSection P a) (t : IntegralSection P b) :
    (s.mul t).toFun = s.toFun * t.toFun := by
  simp only [IntegralSection.toFun, IntegralSection.mul, map_mul, div_mul_div_comm]

theorem toFun_pow {a : ι → ℤ} (s : IntegralSection P a) (m : ℕ) :
    (s.pow m).toFun = s.toFun ^ m := by
  simp only [IntegralSection.toFun, IntegralSection.pow, map_pow, div_pow]

theorem proof : MonomialMap.Statement := by
  intro ι _ _ n P L _ q m r hr g h hg hgs hh hhs
  refine ⟨fun s hs ↦ ?_, fun s₁ s₂ heq ↦ ?_⟩
  · let A := ((L.pow (q * m + r)).mul (L.pow (q - r))).mul ((HermLine.standard n).pow (m + 1))
    let B := ((L.pow q).mul (HermLine.standard n)).pow (m + 1)
    have hdeg : A.deg = B.deg := by
      funext k
      simp only [A, B, HermLine.mul, HermLine.pow, HermLine.standard, Pi.add_apply, Pi.smul_apply,
]
      simp only [nsmul_eq_mul]
      push_cast [Nat.cast_sub hr.le]
      ring
    have hmet : ∀ z, A.metric z = B.metric z := by
      intro z
      simp only [A, B, HermLine.mul, HermLine.pow]
      have hexp : q * m + r + (q - r) = q * (m + 1) := by
        rw [Nat.mul_succ]; omega
      rw [← pow_add, hexp, mul_pow, pow_mul]
    have h₁ := supNormLE_mul (L.pow (q * m + r)) (L.pow (q - r)) s (g.pow (q - r)) hs
      (supNormLE_pow L g hgs (q - r))
    have h₂ := supNormLE_pow (HermLine.standard n) h hhs (m + 1)
    have hA := supNormLE_mul ((L.pow (q * m + r)).mul (L.pow (q - r)))
      ((HermLine.standard n).pow (m + 1)) (s.mul (g.pow (q - r))) (h.pow (m + 1)) h₁ h₂
    have hz : (0 : ℝ) + ((q - r : ℕ) : ℝ) * 0 + ((m + 1 : ℕ) : ℝ) * 0 = 0 := by simp
    rw [hz] at hA
    refine ⟨((s.mul (g.pow (q - r))).mul (h.pow (m + 1))).cast hdeg, ?_, supNormLE_cast A B hdeg hmet _ hA⟩
    change ((s.mul (g.pow (q - r))).mul (h.pow (m + 1))).toFun = _
    rw [toFun_mul, toFun_mul, toFun_pow, toFun_pow]
  · have hne : g.toFun ^ (q - r) * h.toFun ^ (m + 1) ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ hg) (pow_ne_zero _ hh)
    rw [mul_assoc, mul_assoc] at heq
    exact mul_right_cancel₀ hne heq

end MonomialMap

end

end GroundTheory.Heights₂.Heights
