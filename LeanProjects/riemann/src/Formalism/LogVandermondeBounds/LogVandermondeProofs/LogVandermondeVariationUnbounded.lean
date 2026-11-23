import Formalism.LogVandermondeBounds.LogVandermondeVariationUnbounded
import Mathlib

namespace Formalism.LogVandermondeBounds.StandardLattice

open Finset

lemma abs_log_sub_le_of {x y m e : ℝ} (hm : 0 < m) (hx : m ≤ x) (hy : m ≤ y)
    (hxy : |x - y| ≤ e) : |Real.log x - Real.log y| ≤ e / m := by
  have hx0 : 0 < x := lt_of_lt_of_le hm hx
  have hy0 : 0 < y := lt_of_lt_of_le hm hy
  have h1 : Real.log x - Real.log y ≤ (x - y) / y := by
    have := Real.log_le_sub_one_of_pos (div_pos hx0 hy0)
    rw [Real.log_div hx0.ne' hy0.ne'] at this
    rw [sub_div, div_self hy0.ne']; linarith
  have h2 : Real.log y - Real.log x ≤ (y - x) / x := by
    have := Real.log_le_sub_one_of_pos (div_pos hy0 hx0)
    rw [Real.log_div hy0.ne' hx0.ne'] at this
    rw [sub_div, div_self hx0.ne']; linarith
  have he : 0 ≤ e := le_trans (abs_nonneg _) hxy
  have ha := abs_le.mp hxy
  have h3 : (x - y) / y ≤ e / m := by
    rw [div_le_div_iff₀ hy0 hm]
    nlinarith
  have h4 : (y - x) / x ≤ e / m := by
    rw [div_le_div_iff₀ hx0 hm]
    nlinarith
  rw [abs_le]; constructor <;> linarith

lemma abs_log_sub_le_log {x y e : ℝ} (hx : 1 ≤ x) (hy : 1 ≤ y) (hxy : |x - y| ≤ e) :
    |Real.log x - Real.log y| ≤ Real.log (1 + e) := by
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := by linarith
  have ha := abs_le.mp hxy
  have he : 0 ≤ e := le_trans (abs_nonneg _) hxy
  have h1 : Real.log x - Real.log y ≤ Real.log (1 + e) := by
    rw [← Real.log_div hx0.ne' hy0.ne']
    apply Real.log_le_log (div_pos hx0 hy0)
    rw [div_le_iff₀ hy0]; nlinarith
  have h2 : Real.log y - Real.log x ≤ Real.log (1 + e) := by
    rw [← Real.log_div hy0.ne' hx0.ne']
    apply Real.log_le_log (div_pos hy0 hx0)
    rw [div_le_iff₀ hx0]; nlinarith
  rw [abs_le]; constructor <;> linarith

lemma gap_sum {n : ℕ} (u : Fin (n + 2) → ℝ) (g : ℝ)
    (h : ∀ i j : Fin (n + 2), 1 ≤ i.val → j.val = i.val + 1 → j.val ≤ n → g ≤ u i - u j)
    (a : Fin (n + 2)) (ha : 1 ≤ a.val) :
    ∀ m : ℕ, ∀ b : Fin (n + 2), b.val = a.val + m → b.val ≤ n → g * m ≤ u a - u b := by
  intro m
  induction m with
  | zero =>
    intro b hb _
    have : b = a := Fin.ext (by omega)
    subst this; simp
  | succ m ih =>
    intro b hb hbn
    let c : Fin (n + 2) := ⟨a.val + m, by omega⟩
    have h1 := ih c rfl (by simp [c]; omega)
    have h2 := h c b (by simp [c]; omega) (by simp [c]; omega) hbn
    push_cast
    linarith

lemma ind_sum_le {N : ℕ} (a0 b0 : Fin N) (L : ℝ) (hL : 0 ≤ L) :
    ∑ a, ∑ b ∈ univ.filter (fun b => a < b), (if a = a0 ∧ b = b0 then L else 0) ≤ L := by
  calc ∑ a, ∑ b ∈ univ.filter (fun b => a < b), (if a = a0 ∧ b = b0 then L else 0)
      ≤ ∑ a : Fin N, (if a = a0 then L else 0) := by
        apply Finset.sum_le_sum
        intro a _
        by_cases h : a = a0
        · simp only [h, true_and, if_true]
          rw [Finset.sum_ite_eq']
          split_ifs <;> linarith
        · simp [h]
    _ = L := by simp

lemma inner_harm_le {N : ℕ} (a : Fin N) :
    ∑ b ∈ univ.filter (fun b => a < b), (1 : ℝ) / (((b.val - a.val - 1 : ℕ) : ℝ) + 1) ≤
      ∑ i ∈ range N, (1 : ℝ) / ((i : ℝ) + 1) := by
  rw [← Finset.sum_image (f := fun i : ℕ => (1 : ℝ) / ((i : ℝ) + 1))
    (g := fun b : Fin N => b.val - a.val - 1)]
  · apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro i hi
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      obtain ⟨b, _, rfl⟩ := hi
      simp only [Finset.mem_range]; omega
    · intro i _ _; positivity
  · intro b hb c hc hbc
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hb hc
    have hb' : a.val < b.val := hb
    have hc' : a.val < c.val := hc
    simp only at hbc
    exact Fin.ext (by omega)

lemma harm_le (N : ℕ) : ∑ i ∈ range N, (1 : ℝ) / ((i : ℝ) + 1) ≤ 1 + Real.log N := by
  have := harmonic_le_one_add_log N
  simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Nat.cast_add,
    Nat.cast_one] at this
  simpa [one_div] using this

lemma dist_cast {N : ℕ} (a b : Fin N) (h : a < b) :
    ((b.val - a.val - 1 : ℕ) : ℝ) + 1 = (b.val : ℝ) - a.val := by
  have h' : a.val < b.val := h
  have : b.val - a.val - 1 + 1 + a.val = b.val := by omega
  have h2 : (((b.val - a.val - 1 : ℕ) : ℝ) + 1) + (a.val : ℝ) = b.val := by exact_mod_cast this
  linarith

lemma pair_bound {n : ℕ} {Δ : ℝ} {u u' : Fin (n + 2) → ℝ} (hw : WordPair n Δ u u')
    (a b : Fin (n + 2)) (hab : a < b) :
    |Real.log (u a - u b) - Real.log (u' a - u' b)| ≤
      2 / (((b.val - a.val - 1 : ℕ) : ℝ) + 1) +
      ((if a = 0 ∧ b = ⟨1, by omega⟩ then Real.log (1 + Δ) else 0) +
       (if a = ⟨n, by omega⟩ ∧ b = Fin.last (n + 1) then Real.log (1 + Δ) else 0)) := by
  obtain ⟨hΔ, h1, h1', hcl, h0, hl, hg⟩ := hw
  have hL : 0 ≤ Real.log (1 + Δ) := Real.log_nonneg (by linarith)
  have hab' : a.val < b.val := hab
  have hbn : b.val < n + 2 := b.isLt
  rw [dist_cast a b hab]
  have hD := h1 a b hab
  have hD' := h1' a b hab
  have hca := abs_le.mp (hcl a)
  have hcb := abs_le.mp (hcl b)
  have hI0 : 0 ≤ (if a = 0 ∧ b = ⟨1, by omega⟩ then Real.log (1 + Δ) else 0) := by
    split_ifs <;> linarith
  have hI1 : 0 ≤ (if a = ⟨n, by omega⟩ ∧ b = Fin.last (n + 1) then Real.log (1 + Δ) else 0) := by
    split_ifs <;> linarith
  have hablt : (a.val : ℝ) < b.val := by exact_mod_cast hab'
  have hd : 0 < (b.val : ℝ) - a.val := by linarith
  have h2d : 0 ≤ 2 / ((b.val : ℝ) - a.val) := by positivity
  have gu := gap_sum u (3 * Δ) (fun i j hi hj hjn => (hg i j hi hj hjn).1)
  have gu' := gap_sum u' (3 * Δ) (fun i j hi hj hjn => (hg i j hi hj hjn).2)
  rcases (by omega : (a.val = 0 ∧ b.val = n + 1) ∨ (a.val = 0 ∧ b.val = 1) ∨
      (a.val = n ∧ b.val = n + 1) ∨ (a.val = 0 ∧ 2 ≤ b.val ∧ b.val ≤ n) ∨
      (1 ≤ a.val ∧ a.val + 1 ≤ n ∧ b.val = n + 1) ∨ (1 ≤ a.val ∧ b.val ≤ n))
    with hc | hc | hc | hc | hc | hc
  · have ea : a = 0 := Fin.ext (by rw [Fin.val_zero]; omega)
    have eb : b = Fin.last (n + 1) := Fin.ext (by rw [Fin.val_last]; omega)
    rw [← ea] at h0
    rw [← eb] at hl
    have key : |Real.log (u a - u b) - Real.log (u' a - u' b)| = 0 := by
      rw [h0, hl, sub_self, abs_zero]
    linarith
  · have ea : a = 0 := Fin.ext (by rw [Fin.val_zero]; omega)
    have eb : b = ⟨1, by omega⟩ := Fin.ext (by show b.val = 1; omega)
    have hI : (if a = 0 ∧ b = ⟨1, by omega⟩ then Real.log (1 + Δ) else 0) = Real.log (1 + Δ) :=
      if_pos ⟨ea, eb⟩
    rw [← ea] at h0
    have hb : |(u a - u b) - (u' a - u' b)| ≤ Δ := by
      rw [abs_le]; constructor <;> linarith
    have := abs_log_sub_le_log hD hD' hb
    linarith
  · have ea : a = ⟨n, by omega⟩ := Fin.ext (by show a.val = n; omega)
    have eb : b = Fin.last (n + 1) := Fin.ext (by rw [Fin.val_last]; omega)
    have hI : (if a = ⟨n, by omega⟩ ∧ b = Fin.last (n + 1) then Real.log (1 + Δ) else 0) =
        Real.log (1 + Δ) := if_pos ⟨ea, eb⟩
    rw [← eb] at hl
    have hb : |(u a - u b) - (u' a - u' b)| ≤ Δ := by
      rw [abs_le]; constructor <;> linarith
    have := abs_log_sub_le_log hD hD' hb
    linarith
  · have ea : a = 0 := Fin.ext (by rw [Fin.val_zero]; omega)
    let b1 : Fin (n + 2) := ⟨1, by omega⟩
    have hb1 : (0 : Fin (n + 2)) < b1 := by rw [Fin.lt_def, Fin.val_zero]; simp [b1]
    have g1 := gu b1 (by simp [b1]) (b.val - 1) b (by simp [b1]; omega) hc.2.2
    have g1' := gu' b1 (by simp [b1]) (b.val - 1) b (by simp [b1]; omega) hc.2.2
    have e01 := h1 0 b1 hb1
    have e01' := h1' 0 b1 hb1
    rw [← ea] at e01 e01' h0
    have hcast : ((b.val - 1 : ℕ) : ℝ) = (b.val : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]; simp
    rw [hcast] at g1 g1'
    have hav : (a.val : ℝ) = 0 := by exact_mod_cast hc.1
    have hb2 : (2 : ℝ) ≤ b.val := by exact_mod_cast hc.2.1
    have hm : 0 < 3 * Δ * ((b.val : ℝ) - 1) := by
      have : (0 : ℝ) < (b.val : ℝ) - 1 := by linarith
      positivity
    have hb : |(u a - u b) - (u' a - u' b)| ≤ Δ := by
      rw [abs_le]; constructor <;> linarith
    have key := abs_log_sub_le_of hm (by linarith) (by linarith) hb
    have hfin : Δ / (3 * Δ * ((b.val : ℝ) - 1)) ≤ 2 / ((b.val : ℝ) - a.val) := by
      rw [hav, sub_zero, div_le_div_iff₀ hm (by linarith)]
      nlinarith
    linarith
  · let an : Fin (n + 2) := ⟨n, by omega⟩
    have eb : b = Fin.last (n + 1) := Fin.ext (by rw [Fin.val_last]; omega)
    have han : an < Fin.last (n + 1) := by rw [Fin.lt_def, Fin.val_last]; simp [an]
    have g1 := gu a hc.1 (n - a.val) an (by simp [an]; omega) (by simp [an])
    have g1' := gu' a hc.1 (n - a.val) an (by simp [an]; omega) (by simp [an])
    have e01 := h1 an _ han
    have e01' := h1' an _ han
    rw [← eb] at e01 e01' hl
    have hcast : ((n - a.val : ℕ) : ℝ) = (n : ℝ) - a.val := by
      rw [Nat.cast_sub (by omega)]
    rw [hcast] at g1 g1'
    have hbv : (b.val : ℝ) = n + 1 := by exact_mod_cast hc.2.2
    have ha2 : (a.val : ℝ) + 1 ≤ n := by exact_mod_cast hc.2.1
    have hm : 0 < 3 * Δ * ((n : ℝ) - a.val) := by
      have : (0 : ℝ) < (n : ℝ) - a.val := by linarith
      positivity
    have hb : |(u a - u b) - (u' a - u' b)| ≤ Δ := by
      rw [abs_le]; constructor <;> linarith
    have key := abs_log_sub_le_of hm (by linarith) (by linarith) hb
    have hfin : Δ / (3 * Δ * ((n : ℝ) - a.val)) ≤ 2 / ((b.val : ℝ) - a.val) := by
      rw [hbv, div_le_div_iff₀ hm (by linarith)]
      nlinarith
    linarith
  · have g1 := gu a hc.1 (b.val - a.val) b (by omega) hc.2
    have g1' := gu' a hc.1 (b.val - a.val) b (by omega) hc.2
    have hcast : ((b.val - a.val : ℕ) : ℝ) = (b.val : ℝ) - a.val := by
      rw [Nat.cast_sub (by omega)]
    rw [hcast] at g1 g1'
    have hm : 0 < 3 * Δ * ((b.val : ℝ) - a.val) := by positivity
    have hb : |(u a - u b) - (u' a - u' b)| ≤ 2 * Δ := by
      rw [abs_le]; constructor <;> linarith
    have key := abs_log_sub_le_of hm (by linarith) (by linarith) hb
    have hfin : 2 * Δ / (3 * Δ * ((b.val : ℝ) - a.val)) ≤ 2 / ((b.val : ℝ) - a.val) := by
      rw [div_le_div_iff₀ hm hd]
      nlinarith
    linarith

lemma harm_double (N : ℕ) :
    ∑ a : Fin N, ∑ b ∈ univ.filter (fun b => a < b), 2 / (((b.val - a.val - 1 : ℕ) : ℝ) + 1) ≤
      2 * N * (1 + Real.log N) := by
  calc ∑ a : Fin N, ∑ b ∈ univ.filter (fun b => a < b), 2 / (((b.val - a.val - 1 : ℕ) : ℝ) + 1)
      ≤ ∑ a : Fin N, 2 * (1 + Real.log N) := by
        apply Finset.sum_le_sum
        intro a _
        have h := (inner_harm_le a).trans (harm_le N)
        have e : ∑ b ∈ univ.filter (fun b => a < b), 2 / (((b.val - a.val - 1 : ℕ) : ℝ) + 1) =
            2 * ∑ b ∈ univ.filter (fun b => a < b), 1 / (((b.val - a.val - 1 : ℕ) : ℝ) + 1) := by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro b _; ring
        rw [e]; linarith
    _ = 2 * N * (1 + Real.log N) := by simp; ring

theorem variation_exponent_bound : LogVandermondeVariation := by
  intro n Δ u u' hw
  have hΔ := hw.1
  have hL : 0 ≤ Real.log (1 + Δ) := Real.log_nonneg (by linarith)
  have e : vandLog u - vandLog u' = ∑ a, ∑ b ∈ univ.filter (fun b => a < b),
      (Real.log (u a - u b) - Real.log (u' a - u' b)) := by
    unfold vandLog
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro a _
    rw [Finset.sum_sub_distrib]
  rw [e]
  have hsum := harm_double (n + 2)
  have i0 := ind_sum_le (0 : Fin (n + 2)) ⟨1, by omega⟩ (Real.log (1 + Δ)) hL
  have i1 := ind_sum_le (⟨n, by omega⟩ : Fin (n + 2)) (Fin.last (n + 1)) (Real.log (1 + Δ)) hL
  have hlog : 0 ≤ Real.log ((n : ℝ) + 2) := Real.log_nonneg (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
  push_cast at hsum
  calc |∑ a, ∑ b ∈ univ.filter (fun b => a < b), (Real.log (u a - u b) - Real.log (u' a - u' b))|
      ≤ ∑ a, ∑ b ∈ univ.filter (fun b => a < b), |Real.log (u a - u b) - Real.log (u' a - u' b)| :=
        (abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun a _ => abs_sum_le_sum_abs _ _)
    _ ≤ ∑ a, ∑ b ∈ univ.filter (fun b => a < b), (2 / (((b.val - a.val - 1 : ℕ) : ℝ) + 1) +
      ((if a = 0 ∧ b = ⟨1, by omega⟩ then Real.log (1 + Δ) else 0) +
       (if a = ⟨n, by omega⟩ ∧ b = Fin.last (n + 1) then Real.log (1 + Δ) else 0))) := by
        apply Finset.sum_le_sum; intro a _
        apply Finset.sum_le_sum; intro b hb
        exact pair_bound hw a b (by simpa using hb)
    _ = (∑ a : Fin (n + 2), ∑ b ∈ univ.filter (fun b => a < b), 2 / (((b.val - a.val - 1 : ℕ) : ℝ) + 1)) +
        ((∑ a : Fin (n + 2), ∑ b ∈ univ.filter (fun b => a < b),
          (if a = 0 ∧ b = ⟨1, by omega⟩ then Real.log (1 + Δ) else 0)) +
        (∑ a : Fin (n + 2), ∑ b ∈ univ.filter (fun b => a < b),
          (if a = ⟨n, by omega⟩ ∧ b = Fin.last (n + 1) then Real.log (1 + Δ) else 0))) := by
        simp only [Finset.sum_add_distrib]
    _ ≤ 6 * (n + 2) * (1 + Real.log (n + 2)) + 2 * Real.log (1 + Δ) := by
        have : 0 ≤ ((n : ℝ) + 2) * (1 + Real.log ((n : ℝ) + 2)) := by positivity
        nlinarith

theorem variation_in_context : LogVandermondeVariationOfLogLe := by
  intro n Δ u u' hw hΔ
  have h := variation_exponent_bound n Δ u u' hw
  have hlog : 0 ≤ Real.log ((n : ℝ) + 2) := Real.log_nonneg (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
  have : 0 ≤ ((n : ℝ) + 2) * Real.log ((n : ℝ) + 2) := by positivity
  nlinarith

end Formalism.LogVandermondeBounds.StandardLattice
