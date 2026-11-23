import Mathlib
import Formalism.GL3MeanSquares.RankMulPowThreeHalvesLeFourthPower

namespace Formalism.HermitianLattices.GenusMassVolumes

open Finset
open Formalism.LogVandermondeBounds.StandardLattice

private lemma sum_Ico_cast_eq_mul_add_triangular (k j : ℕ) :
    ∑ M ∈ Ico (k + 1) (k + j + 1), (M : ℝ) = (j : ℝ) * k + ((j : ℝ) + 1) * j / 2 := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [show k + (j + 1) + 1 = k + j + 1 + 1 by ring, Finset.sum_Ico_succ_top (by omega), ih]
    push_cast
    ring

theorem mass_coefficients : BracketCoefficients := by
  intro k m hk hm
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  have hk' : (0:ℝ) < k := Nat.cast_pos.mpr hk
  have hI : k - 1 + (j + 1) + 1 = k + j + 1 := by omega
  rw [hI, sum_Ico_cast_eq_mul_add_triangular]
  push_cast
  constructor
  · field_simp <;> ring
  · field_simp <;> ring

theorem log_mass_formula : LogMassFormula := by
  intro f m k vE massk massr Lval hf hm hk hvE hmk hL hmass
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  have hI : k - 1 + (j + 1) + 1 = k + j + 1 := by omega
  rw [hI] at hL hmass ⊢
  have hf' : (0:ℝ) < f := Nat.cast_pos.mpr hf
  have hk' : (0:ℝ) < k := Nat.cast_pos.mpr hk
  have hpi : 0 < vE / Real.pi := div_pos hvE Real.pi_pos
  have h2v : 0 < 2 * vE := by linarith
  have hs : 0 < Real.sqrt ((2 * vE) ^ f) := Real.sqrt_pos.2 (pow_pos h2v f)
  have hA : ∀ M : ℕ, 0 < (((M - 1).factorial : ℕ) : ℝ) * (vE / Real.pi) ^ M := fun M =>
    mul_pos (by exact_mod_cast Nat.factorial_pos _) (pow_pos hpi M)
  have hpos : ∀ M ∈ Finset.Ico (k + 1) (k + j + 1),
      0 < ((((M - 1).factorial : ℕ) : ℝ) * (vE / Real.pi) ^ M) ^ f / Real.sqrt ((2 * vE) ^ f) * Lval M :=
    fun M hM => mul_pos (div_pos (pow_pos (hA M) f) hs) (hL M hM)
  have hterm : ∀ M ∈ Finset.Ico (k + 1) (k + j + 1),
      Real.log (((((M - 1).factorial : ℕ) : ℝ) * (vE / Real.pi) ^ M) ^ f / Real.sqrt ((2 * vE) ^ f) * Lval M) =
        f * Real.log (((M - 1).factorial : ℕ) : ℝ) + f * Real.log (vE / Real.pi) * (M : ℝ)
          - f / 2 * Real.log (2 * vE) + Real.log (Lval M) := by
    intro M hM
    have hfac : (0:ℝ) < (((M - 1).factorial : ℕ) : ℝ) := by exact_mod_cast Nat.factorial_pos _
    rw [Real.log_mul (div_pos (pow_pos (hA M) f) hs).ne' (hL M hM).ne',
      Real.log_div (pow_pos (hA M) f).ne' hs.ne', Real.log_pow, Real.log_mul hfac.ne' (pow_pos hpi M).ne',
      Real.log_pow, Real.log_sqrt (pow_pos h2v f).le, Real.log_pow]
    ring
  have hprod : massr / massk = ∏ M ∈ Finset.Ico (k + 1) (k + j + 1),
      ((((M - 1).factorial : ℕ) : ℝ) * (vE / Real.pi) ^ M) ^ f / Real.sqrt ((2 * vE) ^ f) * Lval M := by
    rw [hmass, mul_div_cancel_left₀ _ hmk.ne']
  have hc : (Finset.Ico (k + 1) (k + j + 1)).card = j := by rw [Nat.card_Ico]; omega
  rw [hprod, Real.log_prod (fun M hM => (hpos M hM).ne'), Finset.sum_congr rfl hterm,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    Finset.sum_const, hc, nsmul_eq_mul, sum_Ico_cast_eq_mul_add_triangular]
  push_cast
  field_simp
  ring

private lemma one_add_inv_pow_le_exp_one (N : ℕ) (hN : 1 ≤ N) :
    (1 + 1 / (N : ℝ)) ^ N ≤ Real.exp 1 := by
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  calc (1 + 1 / (N : ℝ)) ^ N ≤ (Real.exp (1 / N)) ^ N := by
        gcongr
        linarith [Real.add_one_le_exp (1 / (N : ℝ))]
    _ = Real.exp 1 := by rw [← Real.exp_nat_mul, mul_one_div_cancel hN']

theorem mass_corollary : PowerProductTwoSidedBounds := by
  intro f k T X Γ Dstar dstar dM lo hi hf hk hfk2 hT hX hΓ hD hd hXD hlow hup hdM hlo hhi
  have hf' : (0:ℝ) < f := Nat.cast_pos.mpr hf
  have hk' : (0:ℝ) < k := Nat.cast_pos.mpr hk
  have hN : (0:ℝ) < f * k := mul_pos hf' hk'
  have hN1 : 1 ≤ f * k := by simpa using Nat.mul_le_mul hf hk
  have hΓ0 : 0 < Γ := by linarith
  have hT0 : 0 < T := by linarith
  set r : ℝ := -(2:ℝ) / ((f:ℝ) * k) with hr
  set Y : ℝ := X * Γ ^ r with hY
  have hYpos : 0 < Y := mul_pos hX (Real.rpow_pos_of_pos hΓ0 r)
  have hrN : r * ((f * k : ℕ) : ℝ) = -2 := by rw [hr, Nat.cast_mul, div_mul_cancel₀ _ hN.ne']
  have hYN : Y ^ (f * k) = Dstar * (Γ⁻¹) ^ 2 / dstar := by
    rw [hY, mul_pow, hXD, ← Real.rpow_natCast (Γ ^ r), ← Real.rpow_mul hΓ0.le, hrN, Real.rpow_neg hΓ0.le,
      Real.rpow_two, inv_pow]
    ring
  have hdY : dstar * Y ^ (f * k) = Dstar * (Γ⁻¹) ^ 2 := by rw [hYN]; field_simp
  have hTk : 1 ≤ T ^ k := one_le_pow₀ (by linarith)
  have hTkpos : 0 < T ^ k := lt_of_lt_of_le one_pos hTk
  have hB : (T ^ k - 1) ^ f ≤ Y ^ (f * k) * Real.exp 1 := by
    calc (T ^ k - 1) ^ f ≤ (T ^ k) ^ f := by gcongr <;> linarith
      _ = T ^ (f * k) := by rw [← pow_mul, mul_comm]
      _ ≤ (Y * (1 + 1 / ((f:ℝ) * k))) ^ (f * k) := by gcongr <;> linarith
      _ = Y ^ (f * k) * (1 + 1 / ((f * k : ℕ) : ℝ)) ^ (f * k) := by rw [mul_pow, Nat.cast_mul]
      _ ≤ Y ^ (f * k) * Real.exp 1 :=
          mul_le_mul_of_nonneg_left (one_add_inv_pow_le_exp_one _ hN1) (pow_nonneg hYpos.le _)
  have hq : (f:ℝ) * (1 / T ^ k) ≤ 1 / 2 := by
    have h2k : (2:ℝ) ^ k ≤ T ^ k := by gcongr
    have h2f : (2 * f : ℝ) ≤ 2 ^ k := by exact_mod_cast hfk2
    rw [mul_one_div, div_le_iff₀ hTkpos]
    linarith
  have hle1 : 1 / T ^ k ≤ 1 := (div_le_one hTkpos).2 hTk
  have hBer : 1 + (f:ℝ) * (-(1 / T ^ k)) ≤ (1 + -(1 / T ^ k)) ^ f := one_add_mul_le_pow (by linarith) f
  have hfac : T ^ k - 1 = T ^ k * (1 + -(1 / T ^ k)) := by
    rw [mul_add, mul_one, mul_neg, mul_one_div_cancel hTkpos.ne']
    ring
  have hA : Y ^ (f * k) / 2 ≤ (T ^ k - 1) ^ f := by
    have h1 : Y ^ (f * k) ≤ (T ^ k) ^ f := by
      rw [← pow_mul, mul_comm k f]
      exact pow_le_pow_left₀ hYpos.le hlow _
    have h2 : 1 / 2 ≤ (1 + -(1 / T ^ k)) ^ f := by linarith
    have h3 : 0 ≤ (T ^ k) ^ f := pow_nonneg hTkpos.le _
    have h4 := mul_le_mul_of_nonneg_left h2 h3
    calc Y ^ (f * k) / 2 = Y ^ (f * k) * (1 / 2) := by ring
      _ ≤ (T ^ k) ^ f * (1 / 2) := mul_le_mul_of_nonneg_right h1 (by norm_num)
      _ ≤ (T ^ k) ^ f * (1 + -(1 / T ^ k)) ^ f := h4
      _ = (T ^ k - 1) ^ f := by rw [hfac, mul_pow]
  have hΓr : Γ ^ r ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hΓ (by
    rw [hr]; exact div_nonpos_of_nonpos_of_nonneg (by norm_num) hN.le)
  have hYX : Y ≤ X := mul_le_of_le_one_right hX.le hΓr
  have hinv : 1 / ((f:ℝ) * k) ≤ 1 := (div_le_one hN).2 (by exact_mod_cast hN1)
  have hT2X : T ≤ 2 * X := by nlinarith
  have hlogY : Real.log Y = Real.log X + r * Real.log Γ := by
    rw [hY, Real.log_mul hX.ne' (Real.rpow_pos_of_pos hΓ0 r).ne', Real.log_rpow hΓ0]
  have hr2 : r * Real.log Γ = -(2 * Real.log Γ / ((f:ℝ) * k)) := by rw [hr]; ring
  have hYT : Real.log Y ≤ Real.log T := Real.log_le_log hYpos hlow
  have hT2 : Real.log T ≤ Real.log 2 + Real.log X := by
    rw [← Real.log_mul two_ne_zero hX.ne']
    exact Real.log_le_log hT0 hT2X
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hdM, ← hdY]
    calc dstar * Y ^ (f * k) / 2 = dstar * (Y ^ (f * k) / 2) := by ring
      _ ≤ dstar * (T ^ k - 1) ^ f := mul_le_mul_of_nonneg_left hA hd.le
  · rw [hdM, ← hdY]
    calc dstar * (T ^ k - 1) ^ f ≤ dstar * (Y ^ (f * k) * Real.exp 1) := mul_le_mul_of_nonneg_left hB hd.le
      _ = Real.exp 1 * (dstar * Y ^ (f * k)) := by ring
  · linarith
  · linarith

theorem corollary_needs_degree : MeanSquareRequiresDegreeBound := by
  intro c hc
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hc (by norm_num : (1 / 2 : ℝ) < 1)
  have h1 : ((1:ℝ) / 2) ^ (n + 1) < c :=
    lt_of_le_of_lt (pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_succ n)) hn
  have h2 : ((1:ℝ) / 2) ^ (n + 1) * 2 ^ (n + 1) = 1 := by rw [← mul_pow]; norm_num
  have h3 := mul_lt_mul_of_pos_right h1 (pow_pos (by norm_num : (0:ℝ) < 2) (n + 1))
  rw [h2] at h3
  have h4 : (0:ℝ) ≤ 1 / (((n + 1 : ℕ) : ℝ) * ((1 : ℕ) : ℝ)) := by positivity
  refine ⟨n + 1, 1, 2, 2, 1, 2 ^ (n + 1), 1, by omega, le_rfl, le_rfl, by norm_num, le_rfl, by positivity,
    one_pos, by simp, by simp, ?_, ?_⟩
  · rw [Real.one_rpow, mul_one]
    linarith
  · norm_num
    linarith

theorem joint_variation_bound : NormalizedLogRatioVandermondeVariation := by
  intro f k Dstar massk Ipi V u u' hf hk hD hm hI hV
  have hf' : (0:ℝ) < f := Nat.cast_pos.mpr hf
  have hk' : (0:ℝ) < k := Nat.cast_pos.mpr hk
  have hfac : (0:ℝ) < ∏ i ∈ range k, ((i.factorial : ℕ) : ℝ) :=
    Finset.prod_pos fun i _ => by exact_mod_cast Nat.factorial_pos i
  have hF : ∀ x : ℕ → ℝ, 0 < vandN x k → 0 < dimVN x k := fun x hx => by
    unfold dimVN
    exact div_pos hx hfac
  have hlog : ∀ x : ℕ → ℝ, 0 < vandN x k →
      Real.log (dimVN x k) = Real.log (vandN x k) - Real.log (∏ i ∈ range k, ((i.factorial : ℕ) : ℝ)) :=
    fun x hx => by
      unfold dimVN
      rw [Real.log_div hx.ne' hfac.ne']
  have hP : ∀ w : ℕ → ℕ → ℝ, (∀ ρ, ρ < f → 0 < vandN (w ρ) k) →
      Real.log (Dstar / (massk * Ipi * ∏ ρ ∈ range f, dimVN (w ρ) k)) =
        Real.log Dstar - Real.log (massk * Ipi) - ∑ ρ ∈ range f, Real.log (dimVN (w ρ) k) := by
    intro w hw
    have hpos : ∀ ρ ∈ range f, 0 < dimVN (w ρ) k := fun ρ hρ => hF _ (hw ρ (Finset.mem_range.1 hρ))
    rw [Real.log_div hD.ne' (mul_pos (mul_pos hm hI) (Finset.prod_pos hpos)).ne',
      Real.log_mul (mul_pos hm hI).ne' (Finset.prod_pos hpos).ne',
      Real.log_prod (fun ρ hρ => (hpos ρ hρ).ne')]
    ring
  rw [hP u (fun ρ hρ => (hV ρ hρ).1), hP u' (fun ρ hρ => (hV ρ hρ).2.1)]
  have hsum : |∑ ρ ∈ range f, Real.log (dimVN (u ρ) k) - ∑ ρ ∈ range f, Real.log (dimVN (u' ρ) k)| ≤ f * V := by
    rw [← Finset.sum_sub_distrib]
    calc |∑ ρ ∈ range f, (Real.log (dimVN (u ρ) k) - Real.log (dimVN (u' ρ) k))|
        ≤ ∑ ρ ∈ range f, |Real.log (dimVN (u ρ) k) - Real.log (dimVN (u' ρ) k)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ ρ ∈ range f, V := by
        apply Finset.sum_le_sum
        intro ρ hρ
        have h := hV ρ (Finset.mem_range.1 hρ)
        rw [hlog _ h.1, hlog _ h.2.1]
        have e : Real.log (vandN (u ρ) k) - Real.log (∏ i ∈ range k, ((i.factorial : ℕ) : ℝ)) -
            (Real.log (vandN (u' ρ) k) - Real.log (∏ i ∈ range k, ((i.factorial : ℕ) : ℝ))) =
            Real.log (vandN (u ρ) k) - Real.log (vandN (u' ρ) k) := by ring
        rw [e]
        exact h.2.2
      _ = f * V := by simp
  have hN : (0:ℝ) < 1 / ((f:ℝ) * k) := by positivity
  have e : 1 / ((f:ℝ) * k) * (Real.log Dstar - Real.log (massk * Ipi) - ∑ ρ ∈ range f, Real.log (dimVN (u ρ) k)) -
      1 / ((f:ℝ) * k) * (Real.log Dstar - Real.log (massk * Ipi) - ∑ ρ ∈ range f, Real.log (dimVN (u' ρ) k)) =
      1 / ((f:ℝ) * k) * -(∑ ρ ∈ range f, Real.log (dimVN (u ρ) k) - ∑ ρ ∈ range f, Real.log (dimVN (u' ρ) k)) := by
    ring
  rw [e, abs_mul, abs_neg, abs_of_pos hN]
  calc 1 / ((f:ℝ) * k) * |∑ ρ ∈ range f, Real.log (dimVN (u ρ) k) - ∑ ρ ∈ range f, Real.log (dimVN (u' ρ) k)|
      ≤ 1 / ((f:ℝ) * k) * (f * V) := mul_le_mul_of_nonneg_left hsum hN.le
    _ = V / k := by field_simp

end Formalism.HermitianLattices.GenusMassVolumes
