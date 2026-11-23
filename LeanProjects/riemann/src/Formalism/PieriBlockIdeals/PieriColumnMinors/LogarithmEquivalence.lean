import Mathlib
import Formalism.PieriBlockIdeals.ContentDistanceBounds

noncomputable section

open Finset

namespace Formalism.CohomologicalDescent

open Classical

theorem eq_of_dvd_of_abs_lt_sq {L : ℝ} (hL : 0 ≤ L) {n : ℤ} (hn : n ≠ 0) (hnL : ((|n| : ℤ) : ℝ) < L ^ 2)
    {l l' : ℕ} (hl : l.Prime) (hl' : l'.Prime) (hLl : L < (l : ℝ)) (hLl' : L < (l' : ℝ))
    (hd : (l : ℤ) ∣ n) (hd' : (l' : ℤ) ∣ n) : l = l' := by
  by_contra hne
  have hcop : IsCoprime (l : ℤ) (l' : ℤ) := by
    rw [Nat.isCoprime_iff_coprime]
    exact (Nat.coprime_primes hl hl').mpr hne
  have hmul : (l : ℤ) * l' ∣ |n| := by
    rw [dvd_abs]
    exact hcop.mul_dvd hd hd'
  have hle : (l : ℤ) * l' ≤ |n| := Int.le_of_dvd (abs_pos.mpr hn) hmul
  have hle' : (l : ℝ) * l' ≤ ((|n| : ℤ) : ℝ) := by exact_mod_cast hle
  have hsq : L ^ 2 < (l : ℝ) * l' := by
    rw [sq]
    exact mul_lt_mul'' hLl hLl' hL hL
  linarith

theorem largePrimeDivisorCount_holds : PrimeCount := by
  intro L T P hL hT hP
  choose! f hfT hfd using fun l (hl : l ∈ P) => (hP l hl).2.2
  apply Finset.card_le_card_of_injOn f
  · intro l hl
    exact hfT l hl
  · intro l hl l' hl' heq
    have h1 := hT (f l) (hfT l hl)
    refine eq_of_dvd_of_abs_lt_sq hL h1.1 h1.2 (hP l hl).1 (hP l' hl').1 (hP l hl).2.1
      (hP l' hl').2.1 (hfd l hl) ?_
    rw [heq]
    exact hfd l' hl'

theorem residueIndicatorPrimeSum_holds : ISum := by
  intro h L xm xp mB P hL hhL hmB hmx hxx hxh hP
  obtain ⟨P', hP'⟩ : ∃ P' : Finset ℕ,
      P' = P.filter (fun l : ℕ => ∃ y : ℤ, xm ≤ y ∧ y ≤ xp ∧ (l : ℤ) ∣ y - mB) := ⟨_, rfl⟩
  have hmem : ∀ l, l ∈ P' ↔ l ∈ P ∧ ∃ y : ℤ, xm ≤ y ∧ y ≤ xp ∧ (l : ℤ) ∣ y - mB := by
    intro l
    rw [hP', Finset.mem_filter]
  choose! g hg1 hg2 hg3 using fun l (hl : l ∈ P') => ((hmem l).mp hl).2
  have hh1 : (1 : ℝ) ≤ h := by
    have : (1 : ℤ) ≤ h := by omega
    exact_mod_cast this
  have hlogh : 0 ≤ Real.log (h : ℝ) := Real.log_nonneg hh1
  have hterm : ∀ l ∈ P', Real.log (l : ℝ) ≤ Real.log (h : ℝ) := by
    intro l hl
    have hlP := ((hmem l).mp hl).1
    have hpos : 0 < g l - mB := by
      have := hg1 l hl
      omega
    have hdle : (l : ℤ) ≤ g l - mB := Int.le_of_dvd hpos (hg3 l hl)
    have hle : (l : ℤ) ≤ h := by
      have := hg2 l hl
      omega
    have hl0 : (0 : ℝ) < l := by exact_mod_cast (hP l hlP).1.pos
    exact Real.log_le_log hl0 (by exact_mod_cast hle)
  have hcard : P'.card ≤ (Finset.Icc xm xp).card := by
    apply Finset.card_le_card_of_injOn g
    · intro l hl
      exact Finset.mem_Icc.mpr ⟨hg1 l hl, hg2 l hl⟩
    · intro l hl l' hl' heq
      have hlP := ((hmem l).mp hl).1
      have hlP' := ((hmem l').mp hl').1
      have hpos : 0 < g l - mB := by
        have := hg1 l hl
        omega
      have hlt : ((|g l - mB| : ℤ) : ℝ) < L ^ 2 := by
        have h1 : |g l - mB| ≤ (h : ℤ) := by
          rw [abs_of_pos hpos]
          have := hg2 l hl
          omega
        have h2 : ((|g l - mB| : ℤ) : ℝ) ≤ (h : ℝ) := by exact_mod_cast h1
        linarith
      refine eq_of_dvd_of_abs_lt_sq hL hpos.ne' hlt (hP l hlP).1 (hP l' hlP').1 (hP l hlP).2
        (hP l' hlP').2 (hg3 l hl) ?_
      rw [heq]
      exact hg3 l' hl'
  have hcardR : ((Finset.Icc xm xp).card : ℝ) = ((xp - xm : ℤ) : ℝ) + 1 := by
    have h0 : (0 : ℤ) ≤ xp + 1 - xm := by omega
    rw [Int.card_Icc, ← Int.cast_natCast, Int.toNat_of_nonneg h0]
    push_cast
    ring
  have key : ∑ l ∈ P', Real.log (l : ℝ) ≤ (((xp - xm : ℤ) : ℝ) + 1) * Real.log (h : ℝ) := by
    calc ∑ l ∈ P', Real.log (l : ℝ) ≤ ∑ _l ∈ P', Real.log (h : ℝ) := Finset.sum_le_sum hterm
      _ = (P'.card : ℝ) * Real.log (h : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((Finset.Icc xm xp).card : ℝ) * Real.log (h : ℝ) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hlogh
      _ = (((xp - xm : ℤ) : ℝ) + 1) * Real.log (h : ℝ) := by rw [hcardR]
  refine Eq.trans_le ?_ key
  rw [hP', Finset.sum_filter]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  unfold IlInd
  split_ifs <;> simp

end Formalism.CohomologicalDescent
