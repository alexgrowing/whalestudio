import Mathlib
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.RecordEigenInputs
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NineStatements

open Finset

namespace PrimeLogSum

theorem term_le {p : ℕ} (hp : 2 ≤ p) :
    Real.log p / ((p : ℝ) - 1) ≤ 2 * (Real.log p / p) := by
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
  calc Real.log p / ((p : ℝ) - 1) ≤ Real.log p / ((p : ℝ) / 2) :=
        div_le_div_of_nonneg_left (Real.log_natCast_nonneg p) (by positivity) (by linarith)
    _ = 2 * (Real.log p / p) := by ring

theorem block_le (k : ℕ) (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime ∧ Nat.log 2 p = k) :
    ∑ p ∈ S, Real.log p / p ≤ 2 * Real.log 4 := by
  have h1 : ∑ p ∈ S, Real.log p / p ≤ ∑ p ∈ S, Real.log p / (2 : ℝ) ^ k := by
    apply sum_le_sum
    intro p hp
    obtain ⟨hpp, hk⟩ := hS p hp
    apply div_le_div_of_nonneg_left (Real.log_natCast_nonneg p) (by positivity)
    have := Nat.pow_log_le_self 2 hpp.ne_zero
    rw [hk] at this
    exact_mod_cast this
  have h2 : ∑ p ∈ S, Real.log p ≤ Chebyshev.theta ((2 ^ (k + 1) : ℕ) : ℝ) := by
    rw [Chebyshev.theta, Nat.floor_natCast]
    apply sum_le_sum_of_subset_of_nonneg
    · intro p hp
      obtain ⟨hpp, hk⟩ := hS p hp
      have := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) p
      rw [hk] at this
      simp only [mem_filter, mem_Ioc]
      exact ⟨⟨hpp.pos, this.le⟩, hpp⟩
    · intro p _ _
      exact Real.log_natCast_nonneg p
  have h3 := Chebyshev.theta_le_log4_mul_x (x := ((2 ^ (k + 1) : ℕ) : ℝ)) (by positivity)
  have hk : (0 : ℝ) < 2 ^ k := by positivity
  calc ∑ p ∈ S, Real.log p / p ≤ ∑ p ∈ S, Real.log p / (2 : ℝ) ^ k := h1
    _ = (∑ p ∈ S, Real.log p) / (2 : ℝ) ^ k := by rw [sum_div]
    _ ≤ Chebyshev.theta ((2 ^ (k + 1) : ℕ) : ℝ) / (2 : ℝ) ^ k := by gcongr
    _ ≤ Real.log 4 * ((2 ^ (k + 1) : ℕ) : ℝ) / (2 : ℝ) ^ k := by gcongr
    _ = 2 * Real.log 4 := by
      push_cast
      rw [pow_succ]
      field_simp

theorem natLog_mul_log_two_le {N : ℕ} (hN : N ≠ 0) :
    (Nat.log 2 N : ℝ) * Real.log 2 ≤ Real.log N := by
  have h := Nat.pow_log_le_self 2 hN
  have h' : (2 : ℝ) ^ Nat.log 2 N ≤ N := by exact_mod_cast h
  have := Real.log_le_log (by positivity) h'
  rwa [Real.log_pow] at this

theorem small_le {N : ℕ} (hN : 2 ≤ N) (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime ∧ p ≤ N) :
    ∑ p ∈ S, Real.log p / p ≤ 8 * Real.log N := by
  have hmap : ∀ p ∈ S, Nat.log 2 p ∈ range (Nat.log 2 N + 1) := by
    intro p hp
    simp only [mem_range]
    exact Nat.lt_succ_of_le (Nat.log_mono_right (hS p hp).2)
  rw [← Finset.sum_fiberwise_of_maps_to hmap]
  have hblocks : ∑ k ∈ range (Nat.log 2 N + 1), ∑ p ∈ S with Nat.log 2 p = k, Real.log p / p
      ≤ ∑ k ∈ range (Nat.log 2 N + 1), 2 * Real.log 4 := by
    apply sum_le_sum
    intro k _
    apply block_le k
    intro p hp
    simp only [mem_filter] at hp
    exact ⟨(hS p hp.1).1, hp.2⟩
  have hcount : ∑ k ∈ range (Nat.log 2 N + 1), 2 * Real.log 4
      = 2 * Real.log 4 * ((Nat.log 2 N : ℝ) + 1) := by
    simp [sum_const, card_range]
    ring
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast
    ring
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hl2 : Real.log 2 ≤ Real.log N := Real.log_le_log (by norm_num) hN'
  have hnl := natLog_mul_log_two_le (N := N) (by omega)
  have hl2pos : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  calc _ ≤ _ := hblocks
    _ = 2 * Real.log 4 * ((Nat.log 2 N : ℝ) + 1) := hcount
    _ = 4 * ((Nat.log 2 N : ℝ) * Real.log 2 + Real.log 2) := by rw [hlog4]; ring
    _ ≤ 4 * (Real.log N + Real.log N) := by gcongr
    _ ≤ 8 * Real.log N := by linarith

theorem large_le {B : ℕ} (hB : 2 ≤ B) (S : Finset ℕ) (hS : ∀ p ∈ S, B < p) (hcard : S.card ≤ B) :
    ∑ p ∈ S, Real.log p / ((p : ℝ) - 1) ≤ 4 * Real.log B := by
  have hB' : (2 : ℝ) ≤ B := by exact_mod_cast hB
  have he : Real.exp 1 ≤ (B : ℝ) + 1 := by
    have := Real.exp_one_lt_d9
    linarith
  have hterm : ∀ p ∈ S, Real.log p / ((p : ℝ) - 1) ≤ 2 * (Real.log ((B : ℝ) + 1) / ((B : ℝ) + 1)) := by
    intro p hp
    have hBp : B + 1 ≤ p := hS p hp
    have hBp' : (B : ℝ) + 1 ≤ p := by exact_mod_cast hBp
    refine (term_le (by omega)).trans ?_
    have := Real.log_div_self_antitoneOn (Set.mem_Ici.mpr he)
      (Set.mem_Ici.mpr (he.trans hBp')) hBp'
    simp only at this
    linarith
  have hsum := sum_le_sum hterm
  rw [sum_const, nsmul_eq_mul] at hsum
  have hcard' : (S.card : ℝ) ≤ B := by exact_mod_cast hcard
  have hlogpos : 0 ≤ Real.log ((B : ℝ) + 1) := Real.log_nonneg (by linarith)
  have hq : 0 ≤ 2 * (Real.log ((B : ℝ) + 1) / ((B : ℝ) + 1)) := by positivity
  have h1 : (S.card : ℝ) * (2 * (Real.log ((B : ℝ) + 1) / ((B : ℝ) + 1)))
      ≤ 2 * Real.log ((B : ℝ) + 1) := by
    calc (S.card : ℝ) * (2 * (Real.log ((B : ℝ) + 1) / ((B : ℝ) + 1)))
        ≤ ((B : ℝ) + 1) * (2 * (Real.log ((B : ℝ) + 1) / ((B : ℝ) + 1))) := by
          gcongr
          linarith
      _ = 2 * Real.log ((B : ℝ) + 1) := by field_simp
  have h2 : Real.log ((B : ℝ) + 1) ≤ 2 * Real.log B := by
    have h := Real.log_le_log (by linarith : (0 : ℝ) < (B : ℝ) + 1)
      (show (B : ℝ) + 1 ≤ (B : ℝ) ^ 2 by nlinarith)
    rw [Real.log_pow] at h
    push_cast at h
    linarith
  linarith

theorem full : Statement := by
  refine ⟨20, fun B hB P hP hcard => ?_⟩
  rw [← sum_filter_add_sum_filter_not P (fun p => p ≤ B)]
  have hsmall : ∑ p ∈ P with p ≤ B, Real.log p / ((p : ℝ) - 1) ≤ 16 * Real.log B := by
    calc ∑ p ∈ P with p ≤ B, Real.log p / ((p : ℝ) - 1)
        ≤ ∑ p ∈ P with p ≤ B, 2 * (Real.log p / p) := by
          apply sum_le_sum
          intro p hp
          simp only [mem_filter] at hp
          exact term_le (hP p hp.1).two_le
      _ = 2 * ∑ p ∈ P with p ≤ B, Real.log p / p := by rw [mul_sum]
      _ ≤ 2 * (8 * Real.log B) := by
          gcongr
          apply small_le hB
          intro p hp
          simp only [mem_filter] at hp
          exact ⟨hP p hp.1, hp.2⟩
      _ = 16 * Real.log B := by ring
  have hlarge : ∑ p ∈ P with ¬ p ≤ B, Real.log p / ((p : ℝ) - 1) ≤ 4 * Real.log B := by
    apply large_le hB
    · intro p hp
      simp only [mem_filter] at hp
      omega
    · exact (card_filter_le _ _).trans hcard
  linarith

end PrimeLogSum

end GroundTheory.Heights₂.Heights.NineStatements
