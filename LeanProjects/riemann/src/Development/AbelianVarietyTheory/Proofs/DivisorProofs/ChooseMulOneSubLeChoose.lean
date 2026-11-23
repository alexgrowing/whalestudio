import Mathlib

open scoped BigOperators Matrix
open Polynomial

namespace GlobalTheory

theorem choose_mul_one_sub_le_choose (N M D : ℕ) (x : ℝ) (hx : 0 ≤ x) (hDM : D ≤ M) (hMN : M ≤ N)
    (h : (N : ℝ) - M ≤ x * ((N : ℝ) - D + 1)) :
    ∀ k ≤ D, ((N.choose k : ℕ) : ℝ) * (1 - k * x) ≤ ((M.choose k : ℕ) : ℝ) := by
  intro k hk
  induction k with
  | zero => simp
  | succ k ih =>
    have hkD : k ≤ D := by omega
    have ih' := ih hkD
    have hkM : k ≤ M := by omega
    have hkN : k ≤ N := by omega
    have eN : ((N.choose (k + 1) : ℕ) : ℝ) * ((k : ℝ) + 1) = ((N.choose k : ℕ) : ℝ) * ((N : ℝ) - k) := by
      have h := Nat.choose_succ_right_eq N k
      rw [← Nat.cast_sub hkN]
      exact_mod_cast h
    have eM : ((M.choose (k + 1) : ℕ) : ℝ) * ((k : ℝ) + 1) = ((M.choose k : ℕ) : ℝ) * ((M : ℝ) - k) := by
      have h := Nat.choose_succ_right_eq M k
      rw [← Nat.cast_sub hkM]
      exact_mod_cast h
    have hk1 : (k : ℝ) + 1 ≤ D := by exact_mod_cast hk
    have hMN' : (M : ℝ) ≤ N := by exact_mod_cast hMN
    have hkM' : (k : ℝ) ≤ M := by exact_mod_cast hkM
    have hA : (0 : ℝ) ≤ ((N.choose k : ℕ) : ℝ) := by positivity
    have hpos : (0 : ℝ) < (k : ℝ) + 1 := by positivity

    have hbr : (0 : ℝ) ≤ x * ((N : ℝ) - k) + x * k * ((N : ℝ) - M) - ((N : ℝ) - M) := by
      have h1 : x * ((N : ℝ) - D + 1) ≤ x * ((N : ℝ) - k) := by
        apply mul_le_mul_of_nonneg_left _ hx
        linarith
      have h2 : 0 ≤ x * k * ((N : ℝ) - M) := by
        have : (0 : ℝ) ≤ (N : ℝ) - M := by linarith
        positivity
      linarith
    have hstep : ((N.choose k : ℕ) : ℝ) * ((N : ℝ) - k) * (1 - ((k : ℝ) + 1) * x)
        ≤ ((M.choose k : ℕ) : ℝ) * ((M : ℝ) - k) := by
      have h3 : ((N.choose k : ℕ) : ℝ) * (1 - k * x) * ((M : ℝ) - k)
          ≤ ((M.choose k : ℕ) : ℝ) * ((M : ℝ) - k) :=
        mul_le_mul_of_nonneg_right ih' (by linarith)
      have h4 := mul_nonneg hA hbr
      nlinarith [h3, h4]
    have goal' : ((N.choose (k + 1) : ℕ) : ℝ) * (1 - ((k : ℝ) + 1) * x) * ((k : ℝ) + 1)
        ≤ ((M.choose (k + 1) : ℕ) : ℝ) * ((k : ℝ) + 1) := by
      rw [eM]
      calc ((N.choose (k + 1) : ℕ) : ℝ) * (1 - ((k : ℝ) + 1) * x) * ((k : ℝ) + 1)
          = ((N.choose (k + 1) : ℕ) : ℝ) * ((k : ℝ) + 1) * (1 - ((k : ℝ) + 1) * x) := by ring
        _ = ((N.choose k : ℕ) : ℝ) * ((N : ℝ) - k) * (1 - ((k : ℝ) + 1) * x) := by rw [eN]
        _ ≤ _ := hstep
    push_cast
    exact le_of_mul_le_mul_right goal' hpos

theorem share_bound_of_jet_count :
    ∀ (D T a : ℕ) (ρ δ d : ℝ), 2 ≤ D → D + 1 ≤ T → 0 ≤ ρ → ρ ≤ 1 / 2 → T + D + 3 ≤ a → (a : ℝ) ≤ ((T : ℝ) + D + 3) / (1 - ρ) → 0 ≤ δ → 0 ≤ d → d ≤ (((a + D).choose D : ℕ) : ℝ) * δ → (1 - 7 * ((D : ℝ) ^ 2 / T + D * ρ)) * d ≤ (((T - 1).choose D : ℕ) : ℝ) * δ := by
  intro D T a ρ δ d hD hDT hρ0 hρ hTa ha hδ hd0 hd
  have hT1 : 1 ≤ T := by omega
  have hT : (0 : ℝ) < T := by
    have : (1 : ℝ) ≤ T := by exact_mod_cast hT1
    linarith
  have hTr : ((T - 1 : ℕ) : ℝ) = (T : ℝ) - 1 := by
    rw [Nat.cast_sub hT1]
    simp
  have hD2 : (2 : ℝ) ≤ D := by exact_mod_cast hD
  have hTa' : (T : ℝ) + D + 3 ≤ a := by exact_mod_cast hTa
  have hxnn : 0 ≤ 4 * (D : ℝ) / T + ρ := by positivity

  have key := choose_mul_one_sub_le_choose (a + D) (T - 1) D (4 * (D : ℝ) / T + ρ) hxnn
    (by omega) (by omega) (by
      push_cast
      rw [hTr]
      have h1ρ : (0 : ℝ) < 1 - ρ := by linarith
      have hamul : (a : ℝ) * (1 - ρ) ≤ (T : ℝ) + D + 3 := (le_div_iff₀ h1ρ).mp ha
      have h4 : 4 * (D : ℝ) ≤ 4 * (D : ℝ) / T * ((a : ℝ) + 1) := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hT]
        have : (0 : ℝ) ≤ 4 * D := by positivity
        nlinarith
      nlinarith [h4, hamul, hρ0, hD2]) D le_rfl
  have hc : 1 - 7 * ((D : ℝ) ^ 2 / T + D * ρ) ≤ 1 - (D : ℝ) * (4 * (D : ℝ) / T + ρ) := by
    have e : (D : ℝ) * (4 * (D : ℝ) / T + ρ) = 4 * ((D : ℝ) ^ 2 / T) + D * ρ := by ring
    have h1 : 0 ≤ (D : ℝ) ^ 2 / T := by positivity
    have h2 : 0 ≤ (D : ℝ) * ρ := by positivity
    rw [e]
    linarith
  have hB : (0 : ℝ) ≤ (((a + D).choose D : ℕ) : ℝ) * δ := by positivity
  have hC : (0 : ℝ) ≤ (((T - 1).choose D : ℕ) : ℝ) * δ := by positivity
  rcases le_or_gt (1 - 7 * ((D : ℝ) ^ 2 / T + D * ρ)) 0 with h | h
  · have : (1 - 7 * ((D : ℝ) ^ 2 / T + D * ρ)) * d ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h hd0
    linarith
  · calc (1 - 7 * ((D : ℝ) ^ 2 / T + D * ρ)) * d
        ≤ (1 - 7 * ((D : ℝ) ^ 2 / T + D * ρ)) * ((((a + D).choose D : ℕ) : ℝ) * δ) :=
          mul_le_mul_of_nonneg_left hd h.le
      _ ≤ (1 - (D : ℝ) * (4 * (D : ℝ) / T + ρ)) * ((((a + D).choose D : ℕ) : ℝ) * δ) :=
          mul_le_mul_of_nonneg_right hc hB
      _ = ((((a + D).choose D : ℕ) : ℝ) * (1 - (D : ℝ) * (4 * (D : ℝ) / T + ρ))) * δ := by ring
      _ ≤ (((T - 1).choose D : ℕ) : ℝ) * δ := mul_le_mul_of_nonneg_right key hδ

end GlobalTheory
