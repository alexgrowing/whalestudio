import Formalism.GaussJetBounds.GenLogInverse

noncomputable section
open scoped BigOperators

universe u

namespace Formalism.DworkPowerSeriesWeights

open Formalism.IncomingBounds

theorem lw_cast_succ (l d : ℕ) (s : ZMod d) : ((lw l s : ℤ) : ZMod (l + 1)) = 1 := by
  unfold lw
  have hl : ((l : ℤ) : ZMod (l + 1)) = -1 := by
    rw [Int.cast_natCast]
    have h : ((l + 1 : ℕ) : ZMod (l + 1)) = 0 := ZMod.natCast_self _
    rw [Nat.cast_add, Nat.cast_one] at h
    linear_combination h
  split_ifs with h
  · rw [Int.cast_mul, Int.cast_one, one_mul, Int.cast_pow, hl]
    exact Even.neg_one_pow (Nat.even_iff.mpr h)
  · rw [Int.cast_mul, Int.cast_neg, Int.cast_one, Int.cast_pow, hl,
      Odd.neg_one_pow (Nat.odd_iff.mpr (by omega))]
    ring

theorem succ_dvd_total {l d : ℕ} (hl : 1 ≤ l) (hd : Even d) {ι : Type*} (n : ι →₀ ℕ)
    (f : ι → ZMod d)
    (h : ((l ^ d - 1 : ℕ) : ℤ) ∣ ∑ x ∈ n.support, (n x : ℤ) * lw l (f x)) :
    ((l + 1 : ℕ) : ℤ) ∣ ∑ x ∈ n.support, (n x : ℤ) := by
  have hl' : ((l : ℕ) : ZMod (l + 1)) = -1 := by
    have h : ((l + 1 : ℕ) : ZMod (l + 1)) = 0 := ZMod.natCast_self _
    rw [Nat.cast_add, Nat.cast_one] at h
    linear_combination h
  have h1 : ((l ^ d - 1 : ℕ) : ZMod (l + 1)) = 0 := by
    rw [Nat.cast_sub (Nat.one_le_pow _ _ (by omega)), Nat.cast_pow, hl', hd.neg_one_pow, Nat.cast_one,
      sub_self]
  obtain ⟨c, hc⟩ := h
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  have h2 := congrArg (fun z : ℤ => (z : ZMod (l + 1))) hc
  simp only [Int.cast_mul, Int.cast_sum, Int.cast_natCast, lw_cast_succ, mul_one, h1, zero_mul] at h2
  rw [Int.cast_sum]
  simpa only [Int.cast_natCast] using h2

theorem dot_const_wt {ι : Type*} (n : ι →₀ ℕ) (c : ℝ) :
    dot n (fun _ => c) = (∑ x ∈ n.support, (n x : ℝ)) * c := by
  simp only [dot, Finsupp.sum, Finset.sum_mul]

theorem weightQuantization : Quant.{u} := by
  unfold Quant
  intro K _ l d _ hl hd2 hd hl1 hl0 K0 hK0 c hc n hdiv hmono
  have hl2 : 2 ≤ l := hl.two_le
  obtain ⟨m, hm⟩ := succ_dvd_total (f := fun x : V2 d => x.2) (by omega) hd n hdiv
  unfold MonoWtGe at hmono ⊢
  rw [dot_const_wt] at hmono ⊢
  have hL : (2 : ℝ) ≤ l := by exact_mod_cast hl2
  have hNm : (∑ x ∈ n.support, (n x : ℝ)) = ((l : ℝ) + 1) * m := by
    have h := congrArg (fun z : ℤ => (z : ℝ)) hm
    push_cast at h
    exact h
  rw [hNm] at hmono ⊢
  by_cases hc0 : c = 0
  · rw [hc0, norm_zero]
    exact Real.rpow_nonneg hl0.le _
  obtain ⟨k, hk⟩ := hK0 c hc hc0
  rw [hk, ← Real.rpow_intCast] at hmono ⊢
  rw [Real.rpow_le_rpow_left_iff_of_base_lt_one hl0 hl1] at hmono ⊢
  unfold rho at hmono ⊢
  have hL2 : (0 : ℝ) < (l : ℝ) ^ 2 - 1 := by nlinarith
  have hL1 : (0 : ℝ) < (l : ℝ) - 1 := by linarith
  set ρ := 1 / ((l : ℝ) ^ 2 - 1) with hρ
  set q := 1 / ((l : ℝ) - 1) with hq
  have hρ1 : ρ * ((l : ℝ) ^ 2 - 1) = 1 := by rw [hρ]; exact one_div_mul_cancel hL2.ne'
  have hq1 : q * ((l : ℝ) - 1) = 1 := by rw [hq]; exact one_div_mul_cancel hL1.ne'
  have hq0 : 0 < q := by rw [hq]; exact one_div_pos.mpr hL1
  have e1 : ((l : ℝ) + 1) * ρ = q := by
    rw [hρ, hq, mul_one_div, div_eq_div_iff hL2.ne' hL1.ne']
    ring
  have h1 : 1 - ((l : ℝ) + 1) * m ≤ k * ((l : ℝ) ^ 2 - 1) := by
    have h := mul_le_mul_of_nonneg_right hmono hL2.le
    have e : (ρ - ((l : ℝ) + 1) * m * ρ) * ((l : ℝ) ^ 2 - 1) = 1 - ((l : ℝ) + 1) * m := by
      linear_combination (1 - ((l : ℝ) + 1) * m) * hρ1
    linarith
  have h2 : (1 : ℝ) ≤ ((l : ℝ) + 1) * (k * ((l : ℝ) - 1) + m) := by nlinarith
  obtain ⟨z, hz⟩ : ∃ z : ℤ, z = k * ((l : ℤ) - 1) + m := ⟨_, rfl⟩
  have h3 : (1 : ℤ) ≤ ((l : ℤ) + 1) * z := by
    rw [hz]
    exact_mod_cast h2
  have h4 : 1 ≤ z := by
    by_contra hz1
    have hz0 : z ≤ 0 := by omega
    nlinarith
  have h5 : (1 : ℝ) ≤ k * ((l : ℝ) - 1) + m := by
    have h := h4
    rw [hz] at h
    exact_mod_cast h
  have h6 := mul_le_mul_of_nonneg_left h5 hq0.le
  have e2 : q * (k * ((l : ℝ) - 1) + m) = k + q * m := by linear_combination k * hq1
  have e3 : ((l : ℝ) + 1) * m * ρ = q * m := by linear_combination m * e1
  linarith

private theorem cancel_lemma {d : ℕ} {s s' : ZMod d} {a i : ℕ}
    (h : s + ((a + i : ℕ) : ZMod d) = s' + (a : ZMod d)) : s + (i : ZMod d) = s' := by
  rw [Nat.cast_add] at h
  linear_combination h

private theorem odd_of_odd_add_add_self {a i : ℕ} (h : Odd (a + i + a)) : Odd i := by
  obtain ⟨k, hk⟩ := h
  exact ⟨k - a, by omega⟩

private theorem odd_of_odd_self_add_add {a i : ℕ} (h : Odd (a + (a + i))) : Odd i := by
  obtain ⟨k, hk⟩ := h
  exact ⟨k - a, by omega⟩

private theorem exists_dTop_eq_le_of_odd_of_mem {d : ℕ} [NeZero d] {TT : Finset (ZMod d)} {s : ZMod d} {i : ℕ} (hi : Odd i)
    (hm : s + (i : ZMod d) ∈ TT) : ∃ e : ℕ, dTop d TT s = e ∧ e ≤ i := by
  have hle : dTop d TT s ≤ (i : ℕ∞) := by
    unfold dTop
    exact iInf₂_le i ⟨hi, hm⟩
  obtain ⟨e, he⟩ := ENat.ne_top_iff_exists.mp (ne_top_of_le_ne_top (ENat.natCast_ne_top i) hle)
  refine ⟨e, he.symm, ?_⟩
  rw [← he] at hle
  exact_mod_cast hle

theorem dualRadiiInequalities : ThmARadii := by
  unfold ThmARadii
  intro l d _ hl hd2 hd TT sig eps hdual hsig heps hT
  unfold IsDualAll at hdual
  have hL : (1 : ℝ) ≤ l := by exact_mod_cast (by omega : 1 ≤ l)
  have hL0 : (0 : ℝ) < l := by linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s s' α β τ τ' hτ hτ' hodd heq
    rcases le_total β α with h | h
    · obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le h
      have hi := odd_of_odd_add_add_self hodd
      have hs := cancel_lemma heq
      have hD := hdual s i hi
      rw [hs] at hD
      have hb : (1 : ℝ) ≤ (l : ℝ) ^ β := one_le_pow₀ hL
      calc (1 : ℝ) ≤ (l : ℝ) ^ β := hb
        _ = (l : ℝ) ^ β * 1 := (mul_one _).symm
        _ ≤ (l : ℝ) ^ β * ((l : ℝ) ^ i * sig s + sig s') := mul_le_mul_of_nonneg_left hD (by positivity)
        _ = (l : ℝ) ^ β * (l : ℝ) ^ i * sig s + (l : ℝ) ^ β * sig s' := by ring
        _ ≤ (l : ℝ) ^ β * (l : ℝ) ^ i * τ + (l : ℝ) ^ β * τ' :=
          add_le_add (mul_le_mul_of_nonneg_left hτ (by positivity))
            (mul_le_mul_of_nonneg_left hτ' (by positivity))
        _ = (l : ℝ) ^ (β + i) * τ + (l : ℝ) ^ β * τ' := by rw [pow_add]
    · obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le h
      have hi := odd_of_odd_self_add_add hodd
      have hs := cancel_lemma heq.symm
      have hD := hdual s' i hi
      rw [hs] at hD
      have hb : (1 : ℝ) ≤ (l : ℝ) ^ α := one_le_pow₀ hL
      calc (1 : ℝ) ≤ (l : ℝ) ^ α := hb
        _ = (l : ℝ) ^ α * 1 := (mul_one _).symm
        _ ≤ (l : ℝ) ^ α * ((l : ℝ) ^ i * sig s' + sig s) := mul_le_mul_of_nonneg_left hD (by positivity)
        _ = (l : ℝ) ^ α * sig s + (l : ℝ) ^ α * (l : ℝ) ^ i * sig s' := by ring
        _ ≤ (l : ℝ) ^ α * τ + (l : ℝ) ^ α * (l : ℝ) ^ i * τ' :=
          add_le_add (mul_le_mul_of_nonneg_left hτ (by positivity))
            (mul_le_mul_of_nonneg_left hτ' (by positivity))
        _ = (l : ℝ) ^ α * τ + (l : ℝ) ^ (α + i) * τ' := by rw [pow_add]
  · intro s β j τ _ hτ
    have hb : (1 : ℝ) ≤ (l : ℝ) ^ β := one_le_pow₀ hL
    have h1 := mul_le_mul_of_nonneg_left hτ (by positivity : (0 : ℝ) ≤ (l : ℝ) ^ β)
    rw [pow_add]
    nlinarith
  · intro s α j τ _ hτ
    have hb : (1 : ℝ) ≤ (l : ℝ) ^ α := one_le_pow₀ hL
    have hj0 : (0 : ℝ) < (l : ℝ) ^ j := by positivity
    have h1 := mul_le_mul_of_nonneg_left hτ (by positivity : (0 : ℝ) ≤ (l : ℝ) ^ α * (l : ℝ) ^ j)
    have e : (l : ℝ) ^ α * (l : ℝ) ^ j * ((l : ℝ) ^ j)⁻¹ = (l : ℝ) ^ α := by
      rw [mul_assoc, mul_inv_cancel₀ hj0.ne', mul_one]
    have h2 : 0 ≤ (l : ℝ) ^ α * eps s := mul_nonneg (by positivity) (heps s)
    rw [pow_add]
    linarith
  · intro s hs s' hs' α β hodd heq
    rcases le_total β α with h | h
    · obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le h
      have hi := odd_of_odd_add_add_self hodd
      have hss := cancel_lemma heq
      obtain ⟨e, he, hei⟩ := exists_dTop_eq_le_of_odd_of_mem (TT := TT) hi (hss ▸ hs')
      have hε := hT s hs e he
      have hpe : (0 : ℝ) < (l : ℝ) ^ e := by positivity
      have hei' : (l : ℝ) ^ e ≤ (l : ℝ) ^ i := pow_le_pow_right₀ hL hei
      have h1 : (l : ℝ) ^ (β + i) * ((l : ℝ) ^ e)⁻¹ ≤ (l : ℝ) ^ (β + i) * eps s :=
        mul_le_mul_of_nonneg_left hε (by positivity)
      have h2 : (l : ℝ) ^ β ≤ (l : ℝ) ^ (β + i) * ((l : ℝ) ^ e)⁻¹ := by
        rw [pow_add, mul_assoc, le_mul_iff_one_le_right (by positivity), le_mul_inv_iff₀ hpe, one_mul]
        exact hei'
      have hb : (1 : ℝ) ≤ (l : ℝ) ^ β := one_le_pow₀ hL
      have h3 : 0 ≤ (l : ℝ) ^ β * eps s' := mul_nonneg (by positivity) (heps s')
      linarith
    · obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le h
      have hi := odd_of_odd_self_add_add hodd
      have hss := cancel_lemma heq.symm
      obtain ⟨e, he, hei⟩ := exists_dTop_eq_le_of_odd_of_mem (TT := TT) hi (hss ▸ hs)
      have hε := hT s' hs' e he
      have hpe : (0 : ℝ) < (l : ℝ) ^ e := by positivity
      have hei' : (l : ℝ) ^ e ≤ (l : ℝ) ^ i := pow_le_pow_right₀ hL hei
      have h1 : (l : ℝ) ^ (α + i) * ((l : ℝ) ^ e)⁻¹ ≤ (l : ℝ) ^ (α + i) * eps s' :=
        mul_le_mul_of_nonneg_left hε (by positivity)
      have h2 : (l : ℝ) ^ α ≤ (l : ℝ) ^ (α + i) * ((l : ℝ) ^ e)⁻¹ := by
        rw [pow_add, mul_assoc, le_mul_iff_one_le_right (by positivity), le_mul_inv_iff₀ hpe, one_mul]
        exact hei'
      have hb : (1 : ℝ) ≤ (l : ℝ) ^ α := one_le_pow₀ hL
      have h3 : 0 ≤ (l : ℝ) ^ α * eps s := mul_nonneg (by positivity) (heps s)
      linarith

theorem oneLetterRadiusIdentity : OneLetterRadius := by
  unfold OneLetterRadius
  intro l hl
  have hL : (3 : ℝ) ≤ l := by exact_mod_cast hl
  have hL1 : (1 : ℝ) ≤ l := by linarith
  refine ⟨fun α β hodd => ?_, ?_⟩
  · rw [le_div_iff₀ (by positivity), one_mul]
    rcases Nat.eq_zero_or_pos α with ha | ha
    · subst ha
      have hb : 1 ≤ β := by
        rcases hodd with ⟨k, hk⟩
        omega
      have h1 : (l : ℝ) ^ 1 ≤ (l : ℝ) ^ β := pow_le_pow_right₀ hL1 hb
      rw [pow_zero]
      rw [pow_one] at h1
      linarith
    · have h1 : (l : ℝ) ^ 1 ≤ (l : ℝ) ^ α := pow_le_pow_right₀ hL1 ha
      have h2 : (1 : ℝ) ≤ (l : ℝ) ^ β := one_le_pow₀ hL1
      rw [pow_one] at h1
      linarith
  · unfold gam rho
    have h1 : (l : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
    have h2 : (l : ℝ) + 1 ≠ 0 := by linarith
    rw [div_sub_div _ _ h1 h2, div_eq_div_iff (mul_ne_zero h1 h2) h1]
    ring

end Formalism.DworkPowerSeriesWeights
