import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EndOmega
open PowerSeries GlobalTheory.Honda

namespace GlobalTheory.Honda.Lazard

theorem norm_natCast_eq_one_of_not_dvd {K : Type} [NormedField K] [IsUltrametricDist K] {l m : ℕ}
    (hp : l.Prime) (hl : ‖(l : K)‖ < 1) (hm : ¬ l ∣ m) : ‖(m : K)‖ = 1 := by
  have hcop : IsCoprime (l : ℤ) (m : ℤ) :=
    Nat.isCoprime_iff_coprime.2 ((Nat.Prime.coprime_iff_not_dvd hp).2 hm)
  obtain ⟨u, v, huv⟩ := hcop
  have h1 : (u : K) * l + v * m = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → K) huv
  have hu : ‖(u : K)‖ ≤ 1 := IsUltrametricDist.norm_intCast_le_one K u
  have hv : ‖(v : K)‖ ≤ 1 := IsUltrametricDist.norm_intCast_le_one K v
  have hmle : ‖(m : K)‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one K m
  refine le_antisymm hmle ?_
  by_contra hlt
  push_neg at hlt
  have h2 : ‖(1 : K)‖ ≤ max ‖(u : K) * l‖ ‖(v : K) * m‖ := by
    rw [← h1]; exact IsUltrametricDist.norm_add_le_max _ _
  rw [norm_one, norm_mul, norm_mul] at h2
  have ha : ‖(u : K)‖ * ‖(l : K)‖ < 1 :=
    lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) hu) hl
  have hb : ‖(v : K)‖ * ‖(m : K)‖ < 1 :=
    lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) hv) hlt
  exact absurd h2 (not_le.2 (max_lt ha hb))

theorem not_dvd_choose_pow_mul {l : ℕ} (hp : l.Prime) (m : ℕ) (hm : ¬ l ∣ m) :
    ∀ v : ℕ, ¬ l ∣ (l ^ v * m).choose (l ^ v) := by
  haveI := Fact.mk hp
  intro v
  induction v with
  | zero => simpa using hm
  | succ v ih =>
    have h := @Choose.choose_modEq_choose_mod_mul_choose_div_nat (l ^ (v + 1) * m) (l ^ (v + 1)) l _
    have e1 : l ^ (v + 1) * m = l * (l ^ v * m) := by ring
    have e2 : l ^ (v + 1) = l * l ^ v := by ring
    rw [e1, e2, Nat.mul_mod_right, Nat.mul_mod_right, Nat.mul_div_cancel_left _ hp.pos,
      Nat.mul_div_cancel_left _ hp.pos, Nat.choose_zero_right, one_mul] at h
    rw [e1, e2]
    intro hd
    exact ih ((Nat.modEq_zero_iff_dvd.1 (h.symm.trans (Nat.modEq_zero_iff_dvd.2 hd))))

theorem choose_prime_pow_pred {l : ℕ} (hp : l.Prime) (i : ℕ) (hi : 0 < i) :
    ∃ m : ℕ, ¬ l ∣ m ∧ (l ^ i).choose (l ^ (i - 1)) = l * m := by
  have hle : l ^ (i - 1) ≤ l ^ i := Nat.pow_le_pow_right hp.pos (Nat.sub_le _ _)
  have h := hp.emultiplicity_choose_prime_pow_add_emultiplicity hle (pow_ne_zero _ hp.ne_zero)
  rw [emultiplicity_pow_self_of_prime hp.prime] at h
  have h1 : emultiplicity l ((l ^ i).choose (l ^ (i - 1))) = ((1 : ℕ) : ℕ∞) := by
    have : ((i : ℕ) : ℕ∞) = ((1 : ℕ) : ℕ∞) + ((i - 1 : ℕ) : ℕ∞) := by
      rw [← Nat.cast_add]; congr 1; omega
    rw [this] at h
    exact WithTop.add_right_cancel (ENat.coe_ne_top _) h
  rw [emultiplicity_eq_coe] at h1
  obtain ⟨⟨m, hm⟩, hn⟩ := h1
  refine ⟨m, ?_, by simpa using hm⟩
  rintro ⟨c, rfl⟩
  apply hn
  exact ⟨c, by rw [hm]; ring⟩

theorem lazard_binomial : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l : ℕ), l.Prime →
    ‖(l : K)‖ < 1 → ∀ (a : K) (n : ℕ), 2 ≤ n →
    (∀ k, 0 < k → k < n → ‖a * (n.choose k : K)‖ ≤ ‖(l : K)‖) →
    ‖a‖ ≤ ‖(l : K)‖ ∨ (‖a‖ ≤ 1 ∧ ∃ i : ℕ, 0 < i ∧ n = l ^ i) := by
  intro K _ _ _ l hp hl a n hn h
  obtain ⟨e, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd (by omega : n ≠ 0) l hp.one_lt.ne'
  have hlpos : 0 < ‖(l : K)‖ := norm_pos_iff.2 (Nat.cast_ne_zero.2 hp.ne_zero)
  by_cases hm1 : m = 1
  · subst hm1
    simp only [mul_one] at h hn ⊢
    have he : 0 < e := by
      rcases Nat.eq_zero_or_pos e with h0 | h0
      · subst h0; simp at hn
      · exact h0
    refine Or.inr ⟨?_, e, he, rfl⟩
    obtain ⟨c, hc, hch⟩ := choose_prime_pow_pred hp e he
    have hk := h (l ^ (e - 1)) (pow_pos hp.pos _) (Nat.pow_lt_pow_right hp.one_lt (by omega))
    rw [hch, Nat.cast_mul, norm_mul, norm_mul, norm_natCast_eq_one_of_not_dvd hp hl hc, mul_one] at hk
    exact le_of_mul_le_mul_right (by rwa [one_mul]) hlpos
  · left
    have hm0 : m ≠ 0 := by rintro rfl; simp at hn
    have hk := h (l ^ e) (pow_pos hp.pos e)
      (lt_mul_of_one_lt_right (pow_pos hp.pos e) (by omega))
    rwa [norm_mul, norm_natCast_eq_one_of_not_dvd hp hl (not_dvd_choose_pow_mul hp m hm e), mul_one] at hk

end GlobalTheory.Honda.Lazard
