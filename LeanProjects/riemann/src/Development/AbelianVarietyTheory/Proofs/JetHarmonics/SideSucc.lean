import Mathlib

open Finset

namespace GlobalTheory.CloudProd

theorem side_succ (c : ℝ) (δ : ℕ → ℝ) (hc : 1 ≤ c) (n : ℕ)
    (h : ∀ j : ℕ, j < n + 1 → 2 * c * (j : ℝ) ≤ δ j) :
    ∏ j ∈ Finset.range (n + 1), (1 + (1 + c) / max (δ j) 1) ≤ (2 + c) * ((n : ℝ) + 1) := by
  induction n with
  | zero =>
    have h1 : (1 + c) / max (δ 0) 1 ≤ 1 + c :=
      div_le_self (by linarith) (le_max_right _ _)
    simp only [zero_add, Finset.prod_range_one, Nat.cast_zero, mul_one]
    linarith
  | succ m ih =>
    rw [Finset.prod_range_succ]
    have ih' := ih (fun j hj => h j (by omega))
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have hd := h (m + 1) (by omega)
    push_cast at hd ⊢
    have hmax : (1 + c) * ((m : ℝ) + 1) ≤ max (δ (m + 1)) 1 := by
      refine le_trans ?_ (le_trans hd (le_max_left _ _))
      nlinarith
    have hpos : (0 : ℝ) < max (δ (m + 1)) 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
    have hf : (1 + c) / max (δ (m + 1)) 1 ≤ 1 / ((m : ℝ) + 1) := by
      rw [div_le_div_iff₀ hpos (by linarith)]
      linarith
    have hf0 : 0 ≤ 1 + (1 + c) / max (δ (m + 1)) 1 := by positivity
    calc _ ≤ ((2 + c) * ((m : ℝ) + 1)) * (1 + 1 / ((m : ℝ) + 1)) :=
          mul_le_mul ih' (by linarith) hf0 (by positivity)
      _ = (2 + c) * ((m : ℝ) + 1 + 1) := by field_simp

theorem side (c : ℝ) (δ : ℕ → ℝ) (hc : 1 ≤ c) (n : ℕ)
    (h : ∀ j : ℕ, j < n → 2 * c * (j : ℝ) ≤ δ j) :
    ∏ j ∈ Finset.range n, (1 + (1 + c) / max (δ j) 1) ≤ (2 + c) * ((n : ℝ) + 1) := by
  cases n with
  | zero => simp; linarith
  | succ m =>
    refine (side_succ c δ hc m h).trans ?_
    push_cast
    nlinarith

theorem main : ∀ (k : ℕ) (c y : ℝ) (lam : ℕ → ℝ), 1 ≤ k → 1 ≤ c → (∀ s : ℕ, 1 ≤ s → s + 1 ≤ k - 1 → lam (s + 1) + 2 * c ≤ lam s) → ∏ s ∈ Finset.Icc 1 (k - 1), (1 + (1 + c) / max |lam s - y| 1) ≤ ((2 + c) * (k : ℝ)) ^ 2 := by
  intro k c y lam hk hc hstep
  classical
  have mono : ∀ s d : ℕ, 1 ≤ s → s + d ≤ k - 1 → lam (s + d) + 2 * c * (d : ℝ) ≤ lam s := by
    intro s d hs
    induction d with
    | zero => intro _; simp
    | succ e ih =>
      intro hle
      have h1 := ih (by omega)
      have h2 := hstep (s + e) (by omega) (by omega)
      rw [← add_assoc]
      push_cast
      linarith
  obtain ⟨p, hp, hup, hlo⟩ : ∃ p : ℕ, p ≤ k - 1 ∧ (p ≠ 0 → y < lam p) ∧
      (p + 1 ≤ k - 1 → lam (p + 1) ≤ y) := by
    refine ⟨Nat.findGreatest (fun s => y < lam s) (k - 1), Nat.findGreatest_le _, ?_, ?_⟩
    · intro h0
      exact Nat.findGreatest_of_ne_zero (P := fun s => y < lam s) rfl h0
    · intro h1
      exact not_lt.mp (Nat.findGreatest_is_greatest (P := fun s => y < lam s)
        (Nat.lt_succ_self _) h1)
  have hI : Finset.Icc 1 (k - 1) = Finset.Ico 1 k := by
    ext s; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
  rw [hI, ← Finset.prod_Ico_consecutive _ (show 1 ≤ p + 1 by omega) (show p + 1 ≤ k by omega),
    Finset.prod_Ico_eq_prod_range, Finset.prod_Ico_eq_prod_range, Nat.add_sub_cancel,
    ← Finset.prod_range_reflect]
  have hA := side c (fun j => |lam (1 + (p - 1 - j)) - y|) hc p (by
    intro j hj
    have h1 := mono (1 + (p - 1 - j)) j (by omega) (by omega)
    rw [show 1 + (p - 1 - j) + j = p by omega] at h1
    have h2 := hup (by omega)
    refine le_trans ?_ (le_abs_self _)
    linarith)
  have hB := side c (fun j => |lam (p + 1 + j) - y|) hc (k - (p + 1)) (by
    intro j hj
    have h1 := mono (p + 1) j (by omega) (by omega)
    have h2 := hlo (by omega)
    refine le_trans ?_ (neg_le_abs _)
    linarith)
  have e1 : ((p : ℝ) + 1) ≤ k := by exact_mod_cast (show p + 1 ≤ k by omega)
  have e2 : (((k - (p + 1) : ℕ) : ℝ) + 1) ≤ k := by
    exact_mod_cast (show k - (p + 1) + 1 ≤ k by omega)
  have hc2 : (0 : ℝ) ≤ 2 + c := by linarith
  rw [sq]
  refine mul_le_mul (hA.trans (mul_le_mul_of_nonneg_left e1 hc2))
    (hB.trans (mul_le_mul_of_nonneg_left e2 hc2)) ?_ (by positivity)
  exact Finset.prod_nonneg (fun j _ => by positivity)

end GlobalTheory.CloudProd
