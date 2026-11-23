import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.StripInt

open UpperTheory.V.Af.Rs in
private theorem arFact_agree (e e' a b : ℕ → ℂ) (ha : Rec e a) (hb : Rec e' b)
    (hp : ∀ p : ℕ, p.Prime → b p = a p) :
    ∀ n : ℕ, 1 ≤ n → (∀ p : ℕ, p.Prime → p ∣ n → e p = e' p) → b n = a n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hn hdiv
  rcases Nat.lt_or_ge n 2 with h | h
  · have h1 : n = 1 := by omega
    subst h1
    rw [ha.1, hb.1]
  · obtain ⟨p, hpp, hpn⟩ := Nat.exists_prime_and_dvd (show n ≠ 1 by omega)
    obtain ⟨n', rfl⟩ := hpn
    have hn' : 1 ≤ n' := Nat.pos_of_ne_zero (by rintro rfl; simp at hn)
    have hlt : n' < p * n' := by have := hpp.two_le; nlinarith
    have hep : e p = e' p := hdiv p hpp (dvd_mul_right p n')
    have hsub : ∀ q : ℕ, q.Prime → q ∣ n' → e q = e' q :=
      fun q hq hqd => hdiv q hq (dvd_mul_of_dvd_right hqd p)
    have h1 := ha.2 p hpp n' hn'
    have h2 := hb.2 p hpp n' hn'
    have hb' := ih n' hlt hn' hsub
    by_cases hpd : p ∣ n'
    · obtain ⟨t, rfl⟩ := hpd
      have ht : 1 ≤ t := Nat.pos_of_ne_zero (by rintro rfl; simp at hn')
      have hdt : p * t / p = t := Nat.mul_div_cancel_left t hpp.pos
      have hlt' : t < p * t := by have := hpp.two_le; nlinarith
      have hbt := ih t (by nlinarith) ht
        (fun q hq hqd => hsub q hq (dvd_mul_of_dvd_right hqd p))
      rw [if_pos (dvd_mul_right p t), hdt] at h1 h2
      rw [hbt, hb', hp p hpp, ← hep] at h2
      linear_combination h2 - h1
    · rw [if_neg hpd, mul_zero, add_zero] at h1 h2
      rw [hb', hp p hpp] at h2
      rw [h2, h1]

theorem UpperTheory.V.Af.Rs.arFact :
    UpperTheory.V.Af.Rs.ArFact := by
  intro r e e' a b ha hb hp hbad hbd
  refine ⟨{n | b n = a n}, fun n hn => hn, ?_⟩
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hn han
  by_cases hgood : ∀ p : ℕ, p.Prime → p ∣ n → e p = e' p
  · have hag := arFact_agree e e' a b ha hb hp n hn hgood
    exact ⟨n, hag, 1, by ring, by simp, by simp [hag]⟩
  · push_neg at hgood
    obtain ⟨p, hpp, hpn, hne⟩ := hgood
    have hap : a p = 0 := hbad p hpp hne
    have hbp : b p = 0 := by rw [hp p hpp, hap]
    obtain ⟨n'', rfl⟩ := hpn
    have hn'' : 1 ≤ n'' := Nat.pos_of_ne_zero (by rintro rfl; simp at hn)
    have h1 := ha.2 p hpp n'' hn''
    by_cases hpd : p ∣ n''
    · obtain ⟨t, rfl⟩ := hpd
      have ht : 1 ≤ t := Nat.pos_of_ne_zero (by rintro rfl; simp at hn'')
      have hdt : p * t / p = t := Nat.mul_div_cancel_left t hpp.pos
      have h2 := hb.2 p hpp (p * t) hn''
      rw [if_pos (dvd_mul_right p t), hdt, hap, zero_mul] at h1
      rw [if_pos (dvd_mul_right p t), hdt, hbp, zero_mul] at h2
      have hA : a (p * (p * t)) = -(e p * a t) := by linear_combination h1
      have hB : b (p * (p * t)) = -(e' p * b t) := by linear_combination h2
      have hat : a t ≠ 0 := by
        intro h0
        apply han
        rw [hA, h0, mul_zero, neg_zero]
      have hlt : t < p * (p * t) := by have := hpp.two_le; nlinarith
      obtain ⟨n₁, hn₁, m, hnm, hA1, hB1⟩ := ih t hlt ht hat
      refine ⟨n₁, hn₁, p * m, by rw [hnm]; ring, ?_, ?_⟩
      · rw [hA, norm_neg, norm_mul]
        calc ‖e p‖ * ‖a t‖ ≤ (p:ℝ) ^ r * (‖a n₁‖ * (m:ℝ) ^ r) :=
              mul_le_mul (hbd p hpp).1 hA1 (norm_nonneg _) (by positivity)
          _ = ‖a n₁‖ * ((p * m : ℕ) : ℝ) ^ r := by push_cast; ring
      · rw [hB, norm_neg, norm_mul]
        calc ‖e' p‖ * ‖b t‖ ≤ (p:ℝ) ^ r * (‖a n₁‖ * (m:ℝ) ^ r) :=
              mul_le_mul (hbd p hpp).2 hB1 (norm_nonneg _) (by positivity)
          _ = ‖a n₁‖ * ((p * m : ℕ) : ℝ) ^ r := by push_cast; ring
    · exfalso
      apply han
      rw [if_neg hpd, mul_zero, add_zero, hap, zero_mul] at h1
      exact h1
