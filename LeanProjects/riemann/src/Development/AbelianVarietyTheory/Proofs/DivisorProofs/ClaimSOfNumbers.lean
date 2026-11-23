import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import ReciprocityTheory.SemistableReduction.TorusL2CauchyInequality
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

namespace GlobalTheory.HSShortEnd

theorem claimS_of_numbers : ∀ (T D δ d y e : ℕ) (n Λ β Λ₀ ΛD ΛT Hf H' dg : ℝ), 1 ≤ D → D + 1 ≤ T → 1 ≤ δ → 1 ≤ n → 1 ≤ Λ → 1 ≤ β → 1 ≤ Λ₀ → 1 ≤ ΛD → 1 ≤ ΛT → (T - 1).choose D * δ + y ≤ d → ∀ b : ℕ, (D + 1) * b = (T - 1).choose D * (T + D * (D + 1)) → b * ((D + 1) * δ) + e = (T - 1).choose D * δ * T + y * (T - D) → -(cst n Λ * ((D + 1) * δ)) ≤ Hf → -(cst n Λ * e) ≤ H' → b * Hf + H' - (((T - 1).choose D * δ : ℕ) * Real.log (Real.sqrt β ^ T * Λ₀) + y * Real.log (Real.sqrt β ^ (T - D) * ΛD) + (d - (T - 1).choose D * δ - y : ℕ) * Real.log ΛT) ≤ dg → 0 < d ∧ ClaimS T D n Λ β Λ₀ ΛD ΛT δ (Hf / (((D : ℝ) + 1) * δ)) d dg := by
  intro T D δ d y e n Λ β Λ₀ ΛD ΛT Hf H' dg hD hDT hδ hn hΛ hβ hΛ₀ hΛD hΛT hd b hb he hHf hH' hdg
  have hDT' : D ≤ T - 1 := by omega
  have hR : 1 ≤ (T - 1).choose D := Nat.choose_pos hDT'
  set R := (T - 1).choose D with hRdef
  have hRδ : 1 ≤ R * δ := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have hdpos : 0 < d := by omega
  refine ⟨hdpos, ?_⟩

  have hc : 0 ≤ cst n Λ := by
    unfold cst
    have h1 : 0 ≤ Real.log (n * Λ) := Real.log_nonneg (by nlinarith)
    have h2 : 0 ≤ Real.log n := Real.log_nonneg hn
    positivity
  set c := cst n Λ with hcdef

  have hdR : (0 : ℝ) < d := by exact_mod_cast hdpos
  have hδR : (1 : ℝ) ≤ δ := by exact_mod_cast hδ
  have hRR : (1 : ℝ) ≤ R := by exact_mod_cast hR
  have hDR : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hDTR : (D : ℝ) + 1 ≤ T := by exact_mod_cast hDT
  have hdR' : (R : ℝ) * δ + y ≤ d := by exact_mod_cast hd
  have hbR : ((D : ℝ) + 1) * b = R * (T + D * (D + 1)) := by exact_mod_cast hb
  have hTD : D ≤ T := by omega
  have heR : (b : ℝ) * ((D + 1) * δ) + e = R * δ * T + y * ((T : ℝ) - D) := by
    have := congrArg (fun x : ℕ => (x : ℝ)) he
    push_cast [Nat.cast_sub hTD] at this
    linarith
  have hsub : ((d - R * δ - y : ℕ) : ℝ) = d - R * δ - y := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    push_cast; ring
  have hsubTD : ((T - D : ℕ) : ℝ) = T - D := by rw [Nat.cast_sub hTD]

  have hβ0 : 0 < β := by linarith
  have hsq : 0 < Real.sqrt β := Real.sqrt_pos.mpr hβ0
  have hlb : Real.log (Real.sqrt β) = Real.log β / 2 := Real.log_sqrt hβ0.le
  have hL0 : Real.log (Real.sqrt β ^ T * Λ₀) = T * (Real.log β / 2) + Real.log Λ₀ := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, hlb]
  have hLD : Real.log (Real.sqrt β ^ (T - D) * ΛD) = ((T : ℝ) - D) * (Real.log β / 2) + Real.log ΛD := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, hlb, hsubTD]
  have lβ : 0 ≤ Real.log β := Real.log_nonneg hβ
  have lD : 0 ≤ Real.log ΛD := Real.log_nonneg hΛD
  have lT : 0 ≤ Real.log ΛT := Real.log_nonneg hΛT
  have l0 : 0 ≤ Real.log Λ₀ := Real.log_nonneg hΛ₀
  rw [hL0, hLD, hsub] at hdg
  push_cast at hdg

  set h := Hf / (((D : ℝ) + 1) * δ) with hhdef
  have hpos : (0 : ℝ) < ((D : ℝ) + 1) * δ := by positivity
  have hHfh : Hf = ((D : ℝ) + 1) * δ * h := by rw [hhdef]; field_simp
  have hh : -c ≤ h := by
    rw [hhdef, le_div_iff₀ hpos]; linarith
  have hbHf : (b : ℝ) * Hf = R * δ * (T + D * (D + 1)) * h := by
    rw [hHfh]
    calc (b : ℝ) * (((D : ℝ) + 1) * δ * h) = (((D : ℝ) + 1) * b) * δ * h := by ring
      _ = _ := by rw [hbR]; ring

  have he2 : (e : ℝ) = y * ((T : ℝ) - D) - R * δ * (D * (D + 1)) := by
    have : (b : ℝ) * ((D + 1) * δ) = R * δ * (T + D * (D + 1)) := by
      calc (b : ℝ) * ((D + 1) * δ) = (((D : ℝ) + 1) * b) * δ := by ring
        _ = _ := by rw [hbR]; ring
    linarith
  have hy0 : (0 : ℝ) ≤ y := Nat.cast_nonneg y
  have hRδ0 : (0 : ℝ) ≤ R * δ := by positivity
  have hT0 : (0 : ℝ) ≤ T := Nat.cast_nonneg T
  have hD0 : (0 : ℝ) ≤ D := Nat.cast_nonneg D
  have hDD : (0 : ℝ) ≤ D * (D + 1) := by positivity
  have heT : (e : ℝ) ≤ T * (d - R * δ) := by
    rw [he2]
    linarith [mul_nonneg hRδ0 hDD, mul_nonneg hy0 hD0, mul_nonneg (sub_nonneg.mpr hdR') hT0]
  have hce : c * e ≤ c * (T * (d - R * δ)) := mul_le_mul_of_nonneg_left heT hc
  have hch : R * δ * (D * (D + 1)) * (-c) ≤ R * δ * (D * (D + 1)) * h :=
    mul_le_mul_of_nonneg_left hh (mul_nonneg hRδ0 hDD)
  have hX : 0 ≤ (d - R * δ - y) * (T * (Real.log β / 2) + Real.log ΛD) := by
    apply mul_nonneg (by linarith); positivity
  have hyD : 0 ≤ (y : ℝ) * D * Real.log β := by positivity
  have hyT : 0 ≤ (y : ℝ) * Real.log ΛT := by positivity
  have key : (R : ℝ) * δ * (T * h - D * (D + 1) * c - Real.log Λ₀ - T / 2 * Real.log β) -
      (d - R * δ) * (T * c + T / 2 * Real.log β + Real.log ΛD + Real.log ΛT) ≤ dg := by
    linarith [hbHf, hce, hch, hX, hyD, hyT, hdg, hH']
  unfold ClaimS
  have hρ0 : (0 : ℝ) ≤ R * δ / d := div_nonneg hRδ0 hdR.le
  have hρ1 : (R : ℝ) * δ / d ≤ 1 := by rw [div_le_one hdR]; linarith
  refine ⟨by push_cast; linarith, by push_cast; linarith, ?_⟩
  rw [le_div_iff₀ hdR]
  have hdne : (d : ℝ) ≠ 0 := hdR.ne'
  have expand : ((1 - (1 - ((R : ℕ) : ℝ) * δ / d)) * (T * h - D * (D + 1) * c - Real.log Λ₀ - T / 2 * Real.log β) -
      (1 - ((R : ℕ) : ℝ) * δ / d) * (T * c + T / 2 * Real.log β + Real.log ΛD + Real.log ΛT)) * d =
      (R : ℝ) * δ * (T * h - D * (D + 1) * c - Real.log Λ₀ - T / 2 * Real.log β) -
      (d - R * δ) * (T * c + T / 2 * Real.log β + Real.log ΛD + Real.log ΛT) := by
    field_simp
    ring
  push_cast at expand ⊢
  rw [expand]; exact key

end GlobalTheory.HSShortEnd
