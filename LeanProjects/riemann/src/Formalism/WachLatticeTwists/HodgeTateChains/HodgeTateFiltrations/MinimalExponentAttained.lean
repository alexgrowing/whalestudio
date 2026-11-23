import Formalism.WachLatticeTwists.HodgeTateChains.Statement
import Formalism.WindowSums.AnnihilatorPolynomials.ValProd
import Formalism.WindowSums.AnnihilatorPolynomials.ZpowVal

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic

open Polynomial

theorem minimal_exponent_attained : MinimalExponentAttained := by
  intro ℓ hℓ H0
  have hne : {n : ℕ | H0 ≤ ℓ ^ n * (ℓ - 1)}.Nonempty := by
    refine ⟨H0, ?_⟩
    have h1 : H0 < ℓ ^ H0 := Nat.lt_pow_self hℓ.one_lt
    have h2 : 1 ≤ ℓ - 1 := by have := hℓ.two_le; omega
    show H0 ≤ ℓ ^ H0 * (ℓ - 1)
    nlinarith
  refine ⟨Nat.sInf_mem hne, fun n hn => ?_⟩
  have := Nat.notMem_of_lt_sInf hn
  simpa using this

lemma ceilE_spec (d e : ℕ) : e ≤ ceilE (d + 2) e * (d + 1) ∧ ceilE (d + 2) e * (d + 1) < e + (d + 1) := by
  unfold ceilE
  have e1 : d + 2 - 1 = d + 1 := rfl
  rw [e1]
  have h1 := Nat.div_add_mod (e + (d + 1) - 1) (d + 1)
  have h2 := Nat.mod_lt (e + (d + 1) - 1) (Nat.succ_pos d)
  set q := (e + (d + 1) - 1) / (d + 1)
  set r := (e + (d + 1) - 1) % (d + 1)
  have h3 : (d + 1) * q = q * (d + 1) := Nat.mul_comm _ _
  constructor <;> omega

lemma ceilE_le_floor (d e : ℕ) : ceilE (d + 2) e ≤ e / (d + 2 - 1) + 1 := by
  have e1 : d + 2 - 1 = d + 1 := rfl
  rw [e1]
  have h := (ceilE_spec d e).2
  have h1 := Nat.div_add_mod e (d + 1)
  have h2 : e % (d + 1) < d + 1 := Nat.mod_lt e (Nat.succ_pos d)
  by_contra hc
  push Not at hc
  have : (e / (d + 1) + 2) * (d + 1) ≤ ceilE (d + 2) e * (d + 1) := Nat.mul_le_mul_right _ hc
  generalize e / (d + 1) = Q at *
  generalize e % (d + 1) = R at *
  nlinarith

lemma ceilE_le_self (d e : ℕ) : ceilE (d + 2) e ≤ e := by
  have h := (ceilE_spec d e).2
  by_contra hc
  push Not at hc
  have : (e + 1) * (d + 1) ≤ ceilE (d + 2) e * (d + 1) := Nat.mul_le_mul_right _ hc
  nlinarith

theorem ceil : StatCeil := by
  intro ℓ hℓ e
  obtain ⟨d, rfl⟩ : ∃ d, ℓ = d + 2 := ⟨ℓ - 2, by have := hℓ.two_le; omega⟩
  have hD : (((d + 2 : ℕ) : ℚ) - 1) = ((d + 1 : ℕ) : ℚ) := by push_cast; ring
  have hpos : (0 : ℚ) < ((d + 1 : ℕ) : ℚ) := by positivity
  obtain ⟨h1, h2⟩ := ceilE_spec d e
  refine ⟨?_, ?_, ceilE_le_floor d e⟩
  · rw [hD, div_le_iff₀ hpos]; exact_mod_cast h1
  · rw [hD, ← sub_lt_iff_lt_add, lt_div_iff₀ hpos]
    have : ((ceilE (d + 2) e * (d + 1) : ℕ) : ℚ) < ((e + (d + 1) : ℕ) : ℚ) := by exact_mod_cast h2
    push_cast at this ⊢
    linarith

theorem rVal : StatRVal := by
  intro ℓ _ w m hm h2 hw U i
  have key := (Formalism.WindowSums.valProd_of Formalism.WindowSums.valuation_zpow_sub_one ℓ w m hm h2 hw).2
    ((U.erase i).map ⟨fun a => a - i, sub_left_injective⟩) (by
      simp only [Finset.mem_map, Function.Embedding.coeFn_mk, not_exists, not_and]
      intro a ha h0
      exact (Finset.mem_erase.1 ha).1 (by omega))
  have hev : (Rpoly ℓ w U i).eval 1 =
      ∏ a ∈ U.erase i, (1 - ((w ^ (-(a - i)) : ℤ_[ℓ]ˣ) : ℤ_[ℓ])) := by
    unfold Rpoly
    rw [eval_prod]
    refine Finset.prod_congr rfl fun a _ => ?_
    simp [neg_sub]
  rw [Finset.prod_map, Finset.sum_map, Finset.card_map] at key
  simp only [Function.Embedding.coeFn_mk] at key
  rw [hev]
  refine ⟨key.1, ?_⟩
  rw [key.2]
  unfold rI
  rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul]

theorem binom : StatBinom := by
  intro ℓ hℓ b k hb hk hkl
  have hle : k ≤ ℓ ^ b := le_trans hkl.le (Nat.pow_le_pow_right hℓ.pos (by omega))
  have h := hℓ.emultiplicity_choose_prime_pow hle hk.ne'
  have hm : multiplicity ℓ k + 2 ≤ b := by
    by_contra hc
    push Not at hc
    have h1 : ℓ ^ (b - 1) ∣ k :=
      dvd_trans (pow_dvd_pow ℓ (by omega)) (pow_multiplicity_dvd ℓ k)
    exact absurd (Nat.le_of_dvd hk h1) (by omega)
  apply pow_dvd_of_le_emultiplicity
  rw [h]
  exact_mod_cast (by omega : 2 ≤ b - multiplicity ℓ k)

theorem valNN : StatValNN := by
  intro ℓ hℓ s n i j hs hij
  have hl2 : (2 : ℚ) ≤ ℓ := by exact_mod_cast hℓ.two_le
  have hD : (0 : ℚ) < (ℓ : ℚ) - 1 := by linarith
  have hP : (1 : ℚ) ≤ (ℓ : ℚ) ^ (s + n - 1) := one_le_pow₀ (by linarith)
  have hPD : (1 : ℚ) ≤ (ℓ : ℚ) ^ (s + n - 1) * ((ℓ : ℚ) - 1) := by nlinarith
  constructor
  · have hq : (i : ℚ) + j = ℓ * (ℓ : ℚ) ^ (s + n - 1) := by
      have : s + n = (s + n - 1) + 1 := by omega
      rw [this, pow_succ] at hij
      have h' : ((i + j : ℕ) : ℚ) = ((ℓ ^ (s + n - 1) * ℓ : ℕ) : ℚ) := by rw [hij]
      push_cast at h'
      linarith
    have h1 : (ℓ : ℚ) / ((ℓ : ℚ) - 1) =
        ((i : ℚ) + j) / ((ℓ : ℚ) ^ (s + n - 1) * ((ℓ : ℚ) - 1)) := by
      rw [hq]; field_simp
    rw [h1, add_div]
    have : (i : ℚ) / ((ℓ : ℚ) ^ (s + n - 1) * ((ℓ : ℚ) - 1)) ≤ i :=
      div_le_self (by positivity) hPD
    linarith
  · apply lt_min
    · have : 1 / ((ℓ : ℚ) - 1) ≤ 1 := by rw [div_le_one hD]; linarith
      linarith
    · exact div_lt_div_of_pos_right (by linarith) hD

lemma val_factorial_pred (ℓ : ℕ) (hℓ : ℓ.Prime) (e : ℕ) (he : 1 ≤ e) :
    padicValNat ℓ e.factorial = padicValNat ℓ e + padicValNat ℓ (e - 1).factorial := by
  have := Fact.mk hℓ
  rw [← Nat.mul_factorial_pred (by omega : e ≠ 0),
    padicValNat.mul (by omega) (Nat.factorial_ne_zero _)]

theorem betaCount : StatBetaCount := by
  intro ℓ hℓ s e he
  rw [val_factorial_pred ℓ hℓ e he]
  unfold beta
  rw [if_neg (by omega)]
  push_cast
  ring

theorem iBound : StatIBound := by
  intro ℓ hℓ s e
  obtain ⟨d, rfl⟩ : ∃ d, ℓ = d + 2 := ⟨ℓ - 2, by have := hℓ.two_le; omega⟩
  have h := ceilE_le_self d e
  unfold beta
  split_ifs with h0
  · subst h0
    have : ceilE (d + 2) 0 = 0 := by omega
    rw [this]; push_cast; omega
  · have : (ceilE (d + 2) e : ℤ) ≤ e := by exact_mod_cast h
    have h3 : (0 : ℤ) ≤ padicValNat (d + 2) (e - 1).factorial := by positivity
    linarith

lemma cPrime_eq (ℓ : ℕ) (hℓ : ℓ.Prime) (s e : ℕ) :
    cPrime ℓ s e = e * (s + 1) + padicValNat ℓ e.factorial := by
  have := Fact.mk hℓ
  unfold cPrime
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul]
  have h1 : ∑ i ∈ Finset.range e, padicValNat ℓ (e - i) = padicValNat ℓ e.factorial := by
    have hr := Finset.sum_range_reflect (fun j => padicValNat ℓ (j + 1)) e
    have h2 : ∑ j ∈ Finset.range e, padicValNat ℓ (j + 1) = padicValNat ℓ e.factorial := by
      clear hr
      induction e with
      | zero => simp
      | succ k ih =>
        rw [Finset.sum_range_succ, ih, Nat.factorial_succ,
          padicValNat.mul (by omega) (Nat.factorial_ne_zero _)]
        ring
    rw [← h2, ← hr]
    refine Finset.sum_congr rfl fun j hj => ?_
    have := Finset.mem_range.1 hj
    congr 1
    omega
  rw [h1]; ring

theorem aCount : StatACount := by
  intro ℓ hℓ s e
  obtain ⟨d, rfl⟩ : ∃ d, ℓ = d + 2 := ⟨ℓ - 2, by have := hℓ.two_le; omega⟩
  refine ⟨cPrime_eq _ hℓ s e, ?_, ?_⟩
  · rw [cPrime_eq _ hℓ s e]
    unfold beta aTB
    split_ifs with h0
    · subst h0
      have : ceilE (d + 2) 0 = 0 := by have := ceilE_le_self d 0; omega
      rw [this]; simp
    · rw [val_factorial_pred _ hℓ e (by omega)]
      push_cast
      ring
  · unfold aTB
    split_ifs with h0
    · subst h0
      generalize 0 / (d + 2 - 1) = c
      omega
    · have := ceilE_le_floor d e
      omega

theorem cTBTable : StatCTBTable := by
  intro ℓ hℓ s m e gK U
  have := Fact.mk hℓ
  have h1 : cLL ℓ m U 0 ((e : ℤ) + 1) (ℓ ^ (m - s)) = (m - s) + cM ℓ m U 0 ((e : ℤ) + 1) := by
    unfold cLL; rw [padicValNat.prime_pow]
  refine ⟨h1, ?_⟩
  have h2 := (aCount ℓ hℓ s e).2.2
  unfold cTB cTBof
  omega

end Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic
