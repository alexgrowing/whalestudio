import Formalism.PolynomialDimension.DigitClassSize

noncomputable section

open scoped BigOperators
open Finset

namespace Formalism.CountingSumsFrames

theorem hockey_stick_identity : HockeyStick := by
  intro m B
  induction B with
  | zero => simp [dimPol]
  | succ B ih =>
    rw [Finset.sum_range_succ']
    have h1 : ∀ j ∈ range (B + 1), dimPol m (B + 1 - (j + 1)) = dimPol m (B - j) := by
      intro j _
      congr 1
      omega
    rw [Finset.sum_congr rfl h1, ih]
    simp only [dimPol, Nat.sub_zero]
    have : B + 1 + (m + 1) = (B + m + 1) + 1 := by ring
    rw [this, Nat.choose_succ_succ]
    have h2 : B + 1 + m = B + m + 1 := by ring
    have h3 : B + (m + 1) = B + m + 1 := by ring
    rw [h2, h3, add_comm]

def digitSum {m P : ℕ} (τ : Fin m → Fin P) : ℕ := ∑ i, (τ i : ℕ)

theorem digit_class_count : DigitClassCount := by
  intro m P g hP
  obtain ⟨p, rfl⟩ : ∃ p, P = p + 1 := ⟨P - 1, by omega⟩
  let f : (Fin m → Fin (p + 1)) → Fin (p + 1) := fun τ =>
    ⟨(g + p * digitSum τ) % (p + 1), Nat.mod_lt _ (Nat.succ_pos p)⟩
  have hsum : ∀ ρ : Fin (m + 1) → Fin (p + 1),
      (∑ i, (ρ i : ℕ)) = (ρ 0 : ℕ) + digitSum (Fin.tail ρ) := by
    intro ρ
    rw [Fin.sum_univ_succ]
    rfl
  have hcard : (univ : Finset (Fin m → Fin (p + 1))).card = (p + 1) ^ m := by
    simp
  rw [← hcard]
  apply Finset.card_nbij' (fun ρ => Fin.tail ρ) (fun τ => Fin.cons (f τ) τ)
  · intro ρ _
    simp
  · intro τ _
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
    rw [hsum]
    simp only [Fin.cons_zero, Fin.tail_cons, f]
    rw [Nat.mod_add_mod]
    have : g + p * digitSum τ + digitSum τ = g + (p + 1) * digitSum τ := by ring
    rw [this, Nat.add_mul_mod_self_left]
  · intro ρ hρ
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hρ
    rw [hsum] at hρ
    have h0 : f (Fin.tail ρ) = ρ 0 := by
      apply Fin.ext
      simp only [f]
      have hlt : (ρ 0 : ℕ) < p + 1 := (ρ 0).isLt
      have hmod : (ρ 0 : ℕ) + digitSum (Fin.tail ρ) ≡ g [MOD p + 1] := hρ
      have h2 := Nat.ModEq.add_right (p * digitSum (Fin.tail ρ)) hmod
      have h3 : (ρ 0 : ℕ) + digitSum (Fin.tail ρ) + p * digitSum (Fin.tail ρ)
          = (ρ 0 : ℕ) + (p + 1) * digitSum (Fin.tail ρ) := by ring
      rw [h3] at h2
      have h4 : (ρ 0 : ℕ) ≡ g + p * digitSum (Fin.tail ρ) [MOD p + 1] := by
        have h5 : (ρ 0 : ℕ) + (p + 1) * digitSum (Fin.tail ρ) ≡ (ρ 0 : ℕ) [MOD p + 1] := by
          unfold Nat.ModEq
          rw [Nat.add_mul_mod_self_left]
        exact h5.symm.trans h2
      unfold Nat.ModEq at h4
      rw [Nat.mod_eq_of_lt hlt] at h4
      exact h4.symm
    simp only
    rw [h0, Fin.cons_self_tail]
  · intro τ _
    simp

theorem digit_step (P g e : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (hkey : ∀ j : ℕ, (1 - t) * ((g : ℝ) + j + 1) ≤ (P : ℝ) * ((e : ℝ) + j + 1)) :
    ∀ j : ℕ, (1 - (j : ℝ) * t) * ((g + j).choose j : ℝ) ≤ (P : ℝ) ^ j * ((e + j).choose j : ℝ) := by
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
    have hg : ((g + (j + 1)).choose (j + 1) : ℝ) * ((j : ℝ) + 1)
        = ((g : ℝ) + j + 1) * ((g + j).choose j : ℝ) := by
      have := Nat.add_one_mul_choose_eq (g + j) j
      have h' : g + (j + 1) = g + j + 1 := by ring
      rw [h']
      have hc : (((g + j + 1) * (g + j).choose j : ℕ) : ℝ)
          = (((g + j + 1).choose (j + 1) * (j + 1) : ℕ) : ℝ) := by
        rw [this]
      push_cast at hc
      linarith
    have he : ((e + (j + 1)).choose (j + 1) : ℝ) * ((j : ℝ) + 1)
        = ((e : ℝ) + j + 1) * ((e + j).choose j : ℝ) := by
      have := Nat.add_one_mul_choose_eq (e + j) j
      have h' : e + (j + 1) = e + j + 1 := by ring
      rw [h']
      have hc : (((e + j + 1) * (e + j).choose j : ℕ) : ℝ)
          = (((e + j + 1).choose (j + 1) * (j + 1) : ℕ) : ℝ) := by
        rw [this]
      push_cast at hc
      linarith
    have hj1 : (0 : ℝ) < (j : ℝ) + 1 := by positivity
    have hCg : (0 : ℝ) ≤ ((g + j).choose j : ℝ) := by positivity
    have hCe : (0 : ℝ) ≤ ((e + j).choose j : ℝ) := by positivity
    have hRHS : (0 : ℝ) ≤ (P : ℝ) ^ (j + 1) * ((e + (j + 1)).choose (j + 1) : ℝ) := by positivity
    push_cast
    by_cases hneg : 1 - ((j : ℝ) + 1) * t ≤ 0
    · have : (1 - ((j : ℝ) + 1) * t) * ((g + (j + 1)).choose (j + 1) : ℝ) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hneg (by positivity)
      linarith
    push Not at hneg
    have hA : 0 ≤ 1 - (j : ℝ) * t := by nlinarith
    have hB : 0 ≤ 1 - t := by nlinarith
    have hG : (0 : ℝ) ≤ (g : ℝ) + j + 1 := by positivity

    rw [← mul_le_mul_iff_of_pos_right hj1]
    have hL : (1 - ((j : ℝ) + 1) * t) * ((g + (j + 1)).choose (j + 1) : ℝ) * ((j : ℝ) + 1)
        = (1 - ((j : ℝ) + 1) * t) * (((g : ℝ) + j + 1) * ((g + j).choose j : ℝ)) := by
      rw [mul_assoc, hg]
    have hR : (P : ℝ) ^ (j + 1) * ((e + (j + 1)).choose (j + 1) : ℝ) * ((j : ℝ) + 1)
        = ((P : ℝ) ^ j * ((e + j).choose j : ℝ)) * ((P : ℝ) * ((e : ℝ) + j + 1)) := by
      rw [mul_assoc, he, pow_succ]; ring
    rw [hL, hR]
    have h1 : (1 - ((j : ℝ) + 1) * t) ≤ (1 - (j : ℝ) * t) * (1 - t) := by
      nlinarith [mul_nonneg (Nat.cast_nonneg j : (0:ℝ) ≤ j) (mul_nonneg ht ht)]
    calc (1 - ((j : ℝ) + 1) * t) * (((g : ℝ) + j + 1) * ((g + j).choose j : ℝ))
        ≤ ((1 - (j : ℝ) * t) * (1 - t)) * (((g : ℝ) + j + 1) * ((g + j).choose j : ℝ)) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = ((1 - (j : ℝ) * t) * ((g + j).choose j : ℝ)) * ((1 - t) * ((g : ℝ) + j + 1)) := by ring
      _ ≤ ((P : ℝ) ^ j * ((e + j).choose j : ℝ)) * ((P : ℝ) * ((e : ℝ) + j + 1)) :=
          mul_le_mul ih (hkey j) (by positivity) (by positivity)

theorem digit_class_size : DigitClassSize := by
  intro m P g e hP hg he
  have hPr : (1 : ℝ) ≤ P := by exact_mod_cast hP
  have hPpos : (0 : ℝ) < P := by positivity
  have hgpos : (0 : ℝ) < g := by exact_mod_cast hg
  set t : ℝ := ((m : ℝ) + 1) * P / g with ht_def
  have ht : 0 ≤ t := by positivity
  have hgle : (g : ℝ) ≤ P * ((e : ℝ) + (m + 1)) := by
    have : (g : ℝ) / P ≤ (e : ℝ) + (m + 1) := by linarith
    rw [div_le_iff₀ hPpos] at this
    linarith
  have htg : t * g = ((m : ℝ) + 1) * P := by
    rw [ht_def]; field_simp
  have hkey : ∀ j : ℕ, (1 - t) * ((g : ℝ) + j + 1) ≤ (P : ℝ) * ((e : ℝ) + j + 1) := by
    intro j
    have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have htj : 0 ≤ t * ((j : ℝ) + 1) := by positivity
    nlinarith
  have main := digit_step P g e t ht hkey m
  have hdim : ∀ d, (dimPol m d : ℝ) = ((d + m).choose m : ℝ) := fun d => rfl
  rw [hdim, hdim]
  have hfac : 1 - ((m : ℝ) + 1) ^ 2 * P / g ≤ 1 - (m : ℝ) * t := by
    have : ((m : ℝ) + 1) ^ 2 * P / g = ((m : ℝ) + 1) * t := by
      rw [ht_def]; ring
    rw [this]
    nlinarith
  calc (1 - ((m : ℝ) + 1) ^ 2 * P / g) * ((g + m).choose m : ℝ)
      ≤ (1 - (m : ℝ) * t) * ((g + m).choose m : ℝ) :=
        mul_le_mul_of_nonneg_right hfac (by positivity)
    _ ≤ (P : ℝ) ^ m * ((e + m).choose m : ℝ) := main

end Formalism.CountingSumsFrames
