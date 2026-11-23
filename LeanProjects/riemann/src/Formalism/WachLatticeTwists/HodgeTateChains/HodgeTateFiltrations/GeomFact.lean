import Formalism.WachLatticeTwists.HodgeTateChains.StatCharSum
import Formalism.WindowSums.AnnihilatorPolynomials.ZpowVal

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic

theorem kappa : StatKappa := by
  intro ℓ hℓ s ρ hs h2 hρ hρs j hj1 hjs
  have := Fact.mk hℓ
  have hv : padicValNat ℓ j ≤ s := by
    refine le_trans (padicValNat_le_nat_log j) ?_
    calc Nat.log ℓ j ≤ Nat.log ℓ (ℓ ^ s) := Nat.log_mono_right hjs
      _ = s := Nat.log_pow hℓ.one_lt s
  have hvq : (padicValNat ℓ j : ℚ) ≤ s := by exact_mod_cast hv
  rcases Nat.lt_or_ge j 3 with h3 | h3
  · interval_cases j
    · simp only [padicValNat.one]; push_cast; linarith
    · have hv2 : padicValNat ℓ 2 + 1 ≤ s := by
        by_cases hl : ℓ = 2
        · subst hl
          have : padicValNat 2 2 = 1 := padicValNat.self (by norm_num)
          have := h2 rfl
          omega
        · have : padicValNat ℓ 2 = 0 := by
            apply padicValNat.eq_zero_of_not_dvd
            intro hd
            exact hl ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).1 hd)
          omega
      have hv2q : (padicValNat ℓ 2 : ℚ) + 1 ≤ s := by exact_mod_cast hv2
      push_cast
      linarith
  · have hj : (3 : ℚ) ≤ j := by exact_mod_cast h3
    nlinarith

theorem nilDiv : StatNilDiv := by
  intro La _ a b M q hM hnil
  have hb : b = a + (b - a) := by ring
  have hd : (b - a) ^ M = 0 := by
    have : b - a = -(a - b) := by ring
    rw [this, neg_pow, hnil, mul_zero]
  rw [hb, add_pow]
  apply Finset.dvd_sum
  intro m hm
  rw [Finset.mem_range] at hm
  by_cases hq : q ≤ m
  · exact Dvd.dvd.mul_right (Dvd.dvd.mul_right (pow_dvd_pow a hq) _) _
  · have hle : M ≤ q + M - 1 - m := by omega
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hle
    rw [hk, pow_add, hd]
    simp

lemma geom_fact {R : Type} [CommRing R] (x : R) (a b : ℕ) :
    ∑ k ∈ Finset.range (a * b), x ^ k
      = (∑ k ∈ Finset.range a, x ^ k) * ∑ k ∈ Finset.range b, (x ^ a) ^ k := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih, Finset.sum_range_succ, mul_add]
    congr 1
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [pow_add, ← pow_mul, mul_comm]

theorem charSum : StatCharSum := by
  intro R _ ℓ ζ h0 hζ h1 s j i n hjs
  have hpow : ∀ t i, ζ (i + t) ^ (ℓ ^ t) = ζ i := by
    intro t
    induction t with
    | zero => intro i; simp
    | succ t ih =>
      intro i
      rw [pow_succ', pow_mul, ← add_assoc, hζ, ih]
  have hsplit : ∀ k, ζ i ^ (n + ℓ ^ j * k) = ζ i ^ n * (ζ i ^ (ℓ ^ j)) ^ k := by
    intro k; rw [pow_add, pow_mul]
  constructor
  · intro hij
    have hone : ζ i ^ (ℓ ^ j) = 1 := by
      obtain ⟨p, rfl⟩ := Nat.exists_eq_add_of_le hij
      have := hpow i 0
      rw [zero_add, h0] at this
      rw [pow_add, pow_mul, this, one_pow]
    simp only [hsplit, hone, one_pow, mul_one, Finset.sum_const, Finset.card_range]
  · intro hji his
    obtain ⟨t, rfl⟩ : ∃ t, i = j + (t + 1) := ⟨i - j - 1, by omega⟩
    have hy : ζ (j + (t + 1)) ^ (ℓ ^ j) = ζ (t + 1) := by
      rw [add_comm j (t + 1)]; exact hpow j (t + 1)
    simp only [hsplit, hy]
    rw [← Finset.mul_sum]
    obtain ⟨p, hp⟩ : ∃ p, s - j = t + (1 + p) := ⟨s - j - t - 1, by omega⟩
    have hz : ζ (t + 1) ^ (ℓ ^ t) = ζ 1 := by rw [add_comm t 1]; exact hpow t 1
    rw [hp, pow_add, geom_fact, hz, pow_add, pow_one, geom_fact, h1, zero_mul, mul_zero, mul_zero]

theorem rValues : StatRValues := by
  intro ℓ _ u s hs h2 hu e he abelian₂ _ _ L _ _ V β hV ω
  obtain ⟨hne, hval⟩ := Formalism.WindowSums.valuation_zpow_sub_one ℓ u s hs h2 hu (e : ℤ) (by omega)
  rw [zpow_natCast, padicValInt.of_nat] at hval
  rw [zpow_natCast] at hne
  obtain ⟨c, hc⟩ : ∃ c : ℤ_[ℓ]ˣ, (((u ^ e : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) - 1)
      = (c : ℤ_[ℓ]) * (ℓ : ℤ_[ℓ]) ^ (s + padicValNat ℓ e) := by
    have h := PadicInt.unitCoeff_spec hne
    rw [hval] at h
    exact ⟨_, h⟩
  obtain ⟨la, hla1, hla⟩ := hV (fun j =>
    ((ℓ : ℤ_[ℓ]) ^ ((e + 1) * (s - 1) - e * (s - j) - (if j = 1 then s - 1 else s - j + 1))) •
      (β j).symm (((c⁻¹ : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) • ω j))
  refine ⟨la, fun j hj1 hjs => ?_⟩
  have hVj : V j la = ((ℓ : ℤ_[ℓ]) ^ ((e + 1) * (s - 1) - e * (s - j))) •
      (β j).symm (((c⁻¹ : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) • ω j) := by
    by_cases h1 : j = 1
    · subst h1
      rw [hla1, if_pos rfl, smul_smul, ← pow_add]
      congr 2
      have : (e + 1) * (s - 1) = e * (s - 1) + (s - 1) := by ring
      omega
    · rw [hla j (by omega) hjs, if_neg h1, smul_smul, ← pow_add]
      congr 2
      obtain ⟨p, rfl⟩ := Nat.exists_eq_add_of_le hjs
      obtain ⟨j', rfl⟩ : ∃ j', j = j' + 2 := ⟨j - 2, by omega⟩
      have e1 : j' + 2 + p - (j' + 2) = p := by omega
      have e2 : j' + 2 + p - 1 = j' + p + 1 := by omega
      rw [e1, e2]
      have e3 : (e + 1) * (j' + p + 1) = e * p + (p + 1) + (e * j' + e + j') := by ring
      omega
  have hle : e * (s - j) ≤ (e + 1) * (s - 1) := by
    calc e * (s - j) ≤ e * (s - 1) := Nat.mul_le_mul_left _ (by omega)
      _ ≤ (e + 1) * (s - 1) := Nat.mul_le_mul_right _ (by omega)
  rw [hVj, map_smul, LinearEquiv.apply_symm_apply, hc, smul_smul, smul_smul, smul_smul]
  congr 1
  have hexp : (e + 1) * (s - 1) + s + padicValNat ℓ e
      = (s + padicValNat ℓ e) + (e * (s - j) + ((e + 1) * (s - 1) - e * (s - j))) := by omega
  rw [hexp, pow_add, pow_add]
  have hcc : (c : ℤ_[ℓ]) * ((c⁻¹ : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) = 1 := Units.mul_inv c
  linear_combination ((ℓ : ℤ_[ℓ]) ^ (s + padicValNat ℓ e) * ((ℓ : ℤ_[ℓ]) ^ (e * (s - j)) *
    (ℓ : ℤ_[ℓ]) ^ ((e + 1) * (s - 1) - e * (s - j)))) * hcc

end Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic
