import Mathlib
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.HSClaim

namespace GlobalTheory.CovNum

open Formalism.NormVectorIdentities.Items

theorem hsLogRho_bounds (D : ℕ) (n Λ δ h l₀ : ℝ) (hD : 1 ≤ D) (hn : 1 ≤ n) (hΛ : 1 ≤ Λ)
    (hδ : 1 ≤ δ)
    (hl : Real.log Λ + 26 * Real.log (n * D * δ * (1 + Real.log Λ)) ≤ l₀) :
    0 ≤ hsLogRho 26 n D 1 Λ δ h ∧
      hsLogRho 26 n D 1 Λ δ h ≤ l₀ + 26 * Real.log (2 + |h|) := by
  have hD' : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hL : 0 ≤ Real.log Λ := Real.log_nonneg hΛ
  have hh : 0 ≤ |h| := abs_nonneg h
  have h1 : 1 ≤ n * D * δ :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hn hD') hδ
  have h2 : 1 ≤ n * D * δ * (2 + |h| + Real.log Λ) :=
    one_le_mul_of_one_le_of_one_le h1 (by linarith)
  have h3 : n * D * δ * (2 + |h| + Real.log Λ)
      ≤ (n * D * δ * (1 + Real.log Λ)) * (2 + |h|) := by
    rw [mul_assoc (n * D * δ)]
    refine mul_le_mul_of_nonneg_left ?_ (by linarith)
    nlinarith [mul_nonneg hL hh]
  have h4 : Real.log (n * D * δ * (2 + |h| + Real.log Λ))
      ≤ Real.log (n * D * δ * (1 + Real.log Λ)) + Real.log (2 + |h|) := by
    rw [← Real.log_mul (by positivity) (by positivity)]
    exact Real.log_le_log (by linarith) h3
  have h5 := Real.log_nonneg h2
  unfold hsLogRho
  rw [mul_one]
  constructor <;> linarith

theorem deg_lower_of_claim : ∀ (T D : ℕ) (n Λ β ΛD ΛT J δ h d deg z l₀ : ℝ), 1 ≤ T → 1 ≤ D → 1 ≤ n → 1 ≤ Λ → 1 ≤ β → 1 ≤ ΛD → 1 ≤ ΛT → 1 ≤ δ → 0 < d → 0 ≤ z → z ≤ 1 / 2 → (1 - z) * d ≤ ((T - 1).choose D : ℕ) * δ → Real.log Λ + 26 * Real.log (n * D * δ * (1 + Real.log Λ)) ≤ l₀ → Formalism.NormVectorIdentities.Items.HSClaimS 26 T D n 1 Λ β ΛD ΛT J δ h d deg → ((T - 1).choose D : ℕ) * δ * (T * h - 3 * (D + 1) * |h| - 26 * (26 * D ^ 2 + 2 * z * T) * Real.log (2 + |h|) - (J + 26 * D ^ 2 * (l₀ + Real.log T) + (T + D + 1) * Real.log β + (T + D ^ 2) * (Formalism.NormVectorIdentities.Items.hsG D n + 2) + 2 * z * (T * (Real.log 2 + l₀ + Real.log β / 2) + Real.log ΛD + Real.log ΛT))) ≤ deg := by
  intro T D n Λ β ΛD ΛT J δ h d deg z l₀ hT hD hn hΛ hβ hΛD hΛT hδ hd hz hz2 hP hl hc
  obtain ⟨hρ0, hρ⟩ := hsLogRho_bounds D n Λ δ h l₀ hD hn hΛ hδ hl
  obtain ⟨-, -, hc⟩ := hc
  have hT' : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hβ0 : 0 < β := by linarith
  have e1 : Real.log (Real.exp (hsLogRho 26 n D 1 Λ δ h) * T)
      = hsLogRho 26 n D 1 Λ δ h + Real.log T := by
    rw [Real.log_mul (Real.exp_pos _).ne' (by positivity), Real.log_exp]
  have e2 : Real.log (2 * Real.exp (hsLogRho 26 n D 1 Λ δ h) * Real.sqrt β)
      = Real.log 2 + hsLogRho 26 n D 1 Λ δ h + Real.log β / 2 := by
    rw [Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_exp, Real.log_sqrt hβ0.le]
  rw [e1, e2, le_div_iff₀ hd] at hc
  unfold hsZ hsR at hc
  generalize hsLogRho 26 n D 1 Λ δ h = ρ at hρ0 hρ hc
  generalize ((Nat.choose (T - 1) D : ℕ) : ℝ) * δ = P at hP hc ⊢
  generalize hsG D n = g at hc ⊢
  have hb := Real.log_nonneg hβ
  have hLD := Real.log_nonneg hΛD
  have hLT := Real.log_nonneg hΛT
  have h2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  generalize Real.log (2 + |h|) = L at hρ ⊢
  have hdP : d ≤ 2 * P := by nlinarith
  have hP0 : 0 ≤ P := by linarith
  have hdef : d - P ≤ 2 * z * P := by nlinarith
  set A := (T : ℝ) * h - 3 * ((D : ℝ) + 1) * |h| - J - 26 * (D : ℝ) ^ 2 * (ρ + Real.log T)
    - ((T : ℝ) + D + 1) * Real.log β - ((T : ℝ) + (D : ℝ) ^ 2) * (g + 2) with hA
  set B := (T : ℝ) * (Real.log 2 + ρ + Real.log β / 2) + Real.log ΛD + Real.log ΛT with hB
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  have e3 : ((1 - (1 - P / d)) * A - (1 - P / d) * B) * d = P * A - (d - P) * B := by
    field_simp
    ring
  rw [e3] at hc
  have h6 : (d - P) * B ≤ 2 * z * P * B := mul_le_mul_of_nonneg_right hdef hB0
  have h7 : 0 ≤ (26 * (D : ℝ) ^ 2 + 2 * z * T) * (l₀ + 26 * L - ρ) :=
    mul_nonneg (by positivity) (by linarith)
  have h8 : P * (A - 2 * z * B - (26 * (D : ℝ) ^ 2 + 2 * z * T) * (l₀ + 26 * L - ρ))
      ≤ P * (A - 2 * z * B) := mul_le_mul_of_nonneg_left (by linarith) hP0
  refine le_trans (le_of_eq ?_) (h8.trans (by linarith))
  rw [hA, hB]
  ring

end GlobalTheory.CovNum
