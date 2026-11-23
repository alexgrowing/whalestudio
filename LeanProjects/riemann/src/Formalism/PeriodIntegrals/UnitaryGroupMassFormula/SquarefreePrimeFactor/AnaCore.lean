import Mathlib
import Formalism.PeriodIntegrals.PrimesDyadicRS

noncomputable section

namespace PI.SqfPrimeFactor.W

open Finset

lemma ana_log : Real.log 100 < 4.64 := by
  have h2 := Real.log_two_lt_d9
  have h128 : Real.log 128 = 7 * Real.log 2 := by
    rw [show (128 : ℝ) = 2 ^ 7 by norm_num, Real.log_pow]; norm_num
  have hq : Real.log 100 = Real.log 128 - Real.log (128 / 100) := by
    rw [Real.log_div (by norm_num) (by norm_num)]; ring
  have hl : 1 - (128 / 100 : ℝ)⁻¹ ≤ Real.log (128 / 100) :=
    Real.one_sub_inv_le_log_of_pos (by norm_num)
  norm_num at hl h2
  linarith

lemma ana_log_le (x : ℝ) (hx : 100 ≤ x) : Real.log x ≤ 0.0464 * x := by
  have he : Real.exp 1 ≤ 100 := by have := Real.exp_one_lt_d9; linarith
  have h := Real.log_div_self_antitoneOn (Set.mem_Ici.2 he) (Set.mem_Ici.2 (he.trans hx)) hx
  have hx0 : (0 : ℝ) < x := by linarith
  have h100 := ana_log
  simp only at h
  rw [div_le_div_iff₀ hx0 (by norm_num)] at h
  nlinarith

lemma ana_three (r : ℕ) (hr : 100 ≤ r) :
    (({r - 2, r - 1, r} : Finset ℕ).filter Nat.Prime).card ≤ 2 := by
  obtain ⟨e, he, hev, he4⟩ : ∃ e ∈ ({r - 2, r - 1, r} : Finset ℕ), Even e ∧ 4 ≤ e := by
    rcases Nat.even_or_odd r with h | h
    · exact ⟨r, by simp, h, by omega⟩
    · refine ⟨r - 1, by simp, ?_, by omega⟩
      obtain ⟨k, hk⟩ := h
      exact ⟨k, by omega⟩
  have hsub : ({r - 2, r - 1, r} : Finset ℕ).filter Nat.Prime ⊆
      ({r - 2, r - 1, r} : Finset ℕ).erase e := by
    intro x hx
    rw [mem_filter] at hx
    rw [mem_erase]
    refine ⟨?_, hx.1⟩
    rintro rfl
    have := hx.2.eq_one_or_self_of_dvd 2 (even_iff_two_dvd.1 hev)
    omega
  calc _ ≤ _ := card_le_card hsub
    _ = _ := card_erase_of_mem he
    _ ≤ 3 - 1 := Nat.sub_le_sub_right card_le_three 1

lemma ana_pi (r : ℕ) (hr : 100 ≤ r) (S : Finset ℕ)
    (hS : ∀ p, p ∈ S ↔ p.Prime ∧ r < 2 * p ∧ p + 3 ≤ r) :
    Nat.primeCounting r ≤ Nat.primeCounting (r / 2) + S.card + 2 := by
  simp only [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]
  have hsub : (range (r + 1)).filter Nat.Prime ⊆
      ((range (r / 2 + 1)).filter Nat.Prime ∪ S) ∪
        ({r - 2, r - 1, r} : Finset ℕ).filter Nat.Prime := by
    intro p hp
    rw [mem_filter, mem_range] at hp
    obtain ⟨hp1, hpp⟩ := hp
    rw [mem_union, mem_union, mem_filter, mem_filter, mem_range, hS]
    by_cases h1 : p < r / 2 + 1
    · exact Or.inl (Or.inl ⟨h1, hpp⟩)
    by_cases h2 : p + 3 ≤ r
    · exact Or.inl (Or.inr ⟨hpp, by omega, h2⟩)
    refine Or.inr ⟨?_, hpp⟩
    simp only [mem_insert, mem_singleton]
    omega
  calc _ ≤ _ := card_le_card hsub
    _ ≤ _ := card_union_le _ _
    _ ≤ _ := Nat.add_le_add (card_union_le _ _) (ana_three r hr)

theorem ana_main (hRS : PI.PrimesDyadicRS.Claim) (g r : ℕ) (hr : 100 ≤ r) (hg : 2 ^ 12 ≤ g)
    (S : Finset ℕ) (hS : ∀ p, p ∈ S ↔ p.Prime ∧ r < 2 * p ∧ p + 3 ≤ r) :
    (g : ℝ) ^ r - ∑ p ∈ S, ((g : ℝ) ^ p - g) / p * (g : ℝ) ^ (r - p) ≤
      (1 - 1 / (5 * Real.log r)) * (g : ℝ) ^ r := by
  have hrR : (100 : ℝ) ≤ r := by exact_mod_cast hr
  have hR := hRS ((r : ℝ) / 2) (by linarith)
  have hf1 : ⌊2 * ((r : ℝ) / 2)⌋₊ = r := by
    rw [mul_div_cancel₀ _ two_ne_zero]; exact Nat.floor_natCast r
  have hf2 : ⌊(r : ℝ) / 2⌋₊ = r / 2 := by
    rw [Nat.floor_div_ofNat, Nat.floor_natCast]
  rw [hf1, hf2] at hR
  have hcnt : (Nat.primeCounting r : ℝ) ≤ Nat.primeCounting (r / 2) + S.card + 2 := by
    exact_mod_cast ana_pi r hr S hS
  set L := Real.log r with hL
  have hL2 : Real.log ((r : ℝ) / 2) < L := Real.log_lt_log (by linarith) (by linarith)
  have hL2p : 0 < Real.log ((r : ℝ) / 2) := Real.log_pos (by linarith)
  have hLp : 0 < L := by linarith
  have hLle : L ≤ 0.0464 * r := ana_log_le r hrR

  have h3 : 3 * ((r : ℝ) / 2) / (5 * L) ≤ 3 * ((r : ℝ) / 2) / (5 * Real.log ((r : ℝ) / 2)) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
  have hc0 : 3 * ((r : ℝ) / 2) / (5 * L) < S.card + 2 := by linarith
  rw [div_lt_iff₀ (by positivity)] at hc0
  have hcl : (r : ℝ) ≤ S.card * (5 * L) * (4095 / 4096) := by nlinarith

  have hg0 : (4096 : ℝ) ≤ g := by exact_mod_cast hg
  have hgpos : (0 : ℝ) < g := by linarith
  have hrpos : (0 : ℝ) < r := by linarith
  have hterm : ∀ p ∈ S, (g : ℝ) ^ r * (4095 / 4096) / r ≤
      ((g : ℝ) ^ p - g) / p * (g : ℝ) ^ (r - p) := by
    intro p hp
    obtain ⟨hpp, h2, h3⟩ := (hS p).1 hp
    have hp2 : 2 ≤ p := hpp.two_le
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
    have hpr : (p : ℝ) ≤ r := by exact_mod_cast (show p ≤ r by omega)
    have hsplit : (g : ℝ) ^ r = (g : ℝ) ^ p * (g : ℝ) ^ (r - p) := by
      rw [← pow_add]; congr 1; omega
    have hgp2 : (g : ℝ) ^ 2 ≤ (g : ℝ) ^ p := pow_le_pow_right₀ (by linarith) hp2
    have hgp : (g : ℝ) * 4096 ≤ (g : ℝ) ^ p := by nlinarith
    have hq : (0 : ℝ) ≤ (g : ℝ) ^ (r - p) := by positivity
    have hgpp : (0 : ℝ) < (g : ℝ) ^ p := by positivity
    rw [hsplit]
    calc (g : ℝ) ^ p * (g : ℝ) ^ (r - p) * (4095 / 4096) / r
        ≤ (g : ℝ) ^ p * (g : ℝ) ^ (r - p) * (4095 / 4096) / p :=
          div_le_div_of_nonneg_left (by positivity) hp0 hpr
      _ = ((g : ℝ) ^ p * (4095 / 4096)) / p * (g : ℝ) ^ (r - p) := by ring
      _ ≤ ((g : ℝ) ^ p - g) / p * (g : ℝ) ^ (r - p) := by
          apply mul_le_mul_of_nonneg_right _ hq
          apply div_le_div_of_nonneg_right _ hp0.le
          linarith
  have hsum : S.card * ((g : ℝ) ^ r * (4095 / 4096) / r) ≤
      ∑ p ∈ S, ((g : ℝ) ^ p - g) / p * (g : ℝ) ^ (r - p) := by
    have := Finset.sum_le_sum hterm
    rw [Finset.sum_const, nsmul_eq_mul] at this
    exact this
  have hG : (0 : ℝ) < (g : ℝ) ^ r := by positivity
  have hkey : (g : ℝ) ^ r / (5 * L) ≤ S.card * ((g : ℝ) ^ r * (4095 / 4096) / r) := by
    rw [div_le_iff₀ (by positivity)]
    have : S.card * ((g : ℝ) ^ r * (4095 / 4096) / r) * (5 * L) =
        (g : ℝ) ^ r * (S.card * (5 * L) * (4095 / 4096)) / r := by ring
    rw [this, le_div_iff₀ hrpos]
    exact mul_le_mul_of_nonneg_left hcl hG.le
  have : (1 - 1 / (5 * L)) * (g : ℝ) ^ r = (g : ℝ) ^ r - (g : ℝ) ^ r / (5 * L) := by ring
  rw [this]
  linarith

end PI.SqfPrimeFactor.W
