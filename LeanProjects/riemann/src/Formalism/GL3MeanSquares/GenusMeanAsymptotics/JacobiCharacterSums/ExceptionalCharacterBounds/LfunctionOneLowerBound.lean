import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.ExceptionalCharacterBounds.EffAbel
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.ExceptionalCharacterBounds.EffSmooth
import Formalism.LFunctionBounds.LFunctionBoundsProofs.LPartialSum

open Formalism.ZeroFreeDirichlet

noncomputable section

namespace Formalism.HermitianLattices.Ext.SupplyAP

theorem tail_small {x : ℝ} (hx : 1 ≤ x) : x ^ 3 * (x + 1) * Real.exp (-(x ^ 3) / x) ≤ 48 / x ^ 4 := by
  have hx0 : 0 < x := by linarith
  have hdiv : -(x ^ 3) / x = -(x ^ 2) := by field_simp
  rw [hdiv, Real.exp_neg]
  have he := Real.pow_div_factorial_le_exp (x ^ 2) (sq_nonneg x) 4
  have h24 : ((4 : ℕ).factorial : ℝ) = 24 := by norm_num [Nat.factorial]
  rw [h24] at he
  have hE : 0 < Real.exp (x ^ 2) := Real.exp_pos _
  rw [le_div_iff₀ (by positivity), mul_assoc, mul_assoc]
  have hx1 : x + 1 ≤ 2 * x := by linarith
  have hpos : 0 < (Real.exp (x ^ 2))⁻¹ := inv_pos.mpr hE
  have key : x ^ 3 * (x + 1) * x ^ 4 ≤ 2 * x ^ 8 := by nlinarith [pow_pos hx0 7]
  have h8 : x ^ 8 ≤ 24 * Real.exp (x ^ 2) := by
    have : (x ^ 2) ^ 4 = x ^ 8 := by ring
    rw [this] at he
    rw [div_le_iff₀ (by norm_num)] at he; linarith
  calc x ^ 3 * ((x + 1) * ((Real.exp (x ^ 2))⁻¹ * x ^ 4))
      = (x ^ 3 * (x + 1) * x ^ 4) * (Real.exp (x ^ 2))⁻¹ := by ring
    _ ≤ (2 * x ^ 8) * (Real.exp (x ^ 2))⁻¹ := mul_le_mul_of_nonneg_right key hpos.le
    _ ≤ (2 * (24 * Real.exp (x ^ 2))) * (Real.exp (x ^ 2))⁻¹ :=
        mul_le_mul_of_nonneg_right (by linarith) hpos.le
    _ = 48 := by field_simp; ring

theorem lfunction_one_lower_bound (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (hχ2 : χ ^ 2 = 1) (hχ : χ ≠ 1) :
    1 / (20 * ((q : ℝ) + 1)) ≤ (DirichletCharacter.LFunction χ 1).re := by
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  set B : ℝ := (q : ℝ) + 1 with hB
  have hB2 : 2 ≤ B := by linarith
  set Kn : ℕ := 2 * (q + 1) with hKn
  set Nn : ℕ := Kn ^ 6 with hNn
  have hKr : (Kn : ℝ) = 2 * B := by rw [hKn, hB]; push_cast; ring
  set x : ℝ := (Kn : ℝ) ^ 2 with hx
  have hxB : x = 4 * B ^ 2 := by rw [hx, hKr]; ring
  have hx16 : 16 ≤ x := by rw [hxB]; nlinarith
  have hx0 : 0 < x := by linarith
  have hNr : (Nn : ℝ) = x ^ 3 := by rw [hNn, hx]; push_cast; ring
  have hKN : Kn ^ 2 ≤ Nn := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hs := smoothLower q χ hχ2 Kn Nn x hx0 le_rfl hKN
  have ha := abelG q χ hχ x hx0 Nn
  have hGre := (Complex.re_le_norm _).trans ha
  have hN1 : 1 ≤ Nn := Nat.one_le_pow _ _ (by omega)
  have hP := Formalism.FX.l_function_partial_sum q χ hχ ((q : ℝ) + 1)
    (fun M => norm_character_sum_Icc_le χ hχ M) 1 (by norm_num) Nn hN1
  simp only [norm_one, Complex.one_re, div_one] at hP
  have hsum : ∑ n ∈ Finset.Icc 1 Nn, χ (n : ZMod q) * (n : ℂ) ^ (-(1 : ℂ)) =
      ∑ d ∈ Finset.Icc 1 Nn, χ (d : ZMod q) / (d : ℂ) := by
    refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [Complex.cpow_neg_one, div_eq_mul_inv]
  rw [hsum] at hP
  set P := ∑ d ∈ Finset.Icc 1 Nn, χ (d : ZMod q) / (d : ℂ) with hPdef
  set R := (DirichletCharacter.LFunction χ 1).re with hR
  have hNpow : (Nn : ℝ) ^ (-(1 : ℝ)) = x⁻¹ ^ 3 := by
    rw [Real.rpow_neg_one, hNr, inv_pow]
  rw [hNpow] at hP
  have hPre : P.re ≤ R + 2 * ((q : ℝ) + 1) * (1 + 1) * x⁻¹ ^ 3 := by
    have h1 : (P - DirichletCharacter.LFunction χ 1).re ≤ ‖P - DirichletCharacter.LFunction χ 1‖ :=
      Complex.re_le_norm _
    rw [Complex.sub_re, norm_sub_rev] at h1
    have h1' : P.re - R ≤ ‖DirichletCharacter.LFunction χ 1 - P‖ := h1
    linarith
  have htail := tail_small (x := x) (by linarith)
  rw [← hNr] at htail
  have he : Real.exp 1 ≤ (68 / 25 : ℝ) := by have := Real.exp_one_lt_d9; linarith
  have hKe : 2 * B / (68 / 25 : ℝ) ≤ (Kn : ℝ) / Real.exp 1 := by
    rw [hKr]; exact div_le_div_of_nonneg_left (by linarith) (Real.exp_pos 1) he
  have hx3 : x * (2 * B * 2 * x⁻¹ ^ 3) ≤ 1 / 32 := by
    have : x * (2 * B * 2 * x⁻¹ ^ 3) = 4 * B / x ^ 2 := by field_simp; ring_nf
    rw [this, div_le_iff₀ (by positivity), hxB]
    nlinarith [pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) hB2 3]
  have h48 : 48 / x ^ 4 ≤ 1 / 1000 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 16) hx16 4]
  have hmono : x * P.re ≤ x * (R + 2 * B * 2 * x⁻¹ ^ 3) := by
    apply mul_le_mul_of_nonneg_left _ hx0.le
    have h2 : 2 * ((q : ℝ) + 1) * (1 + 1) * x⁻¹ ^ 3 = 2 * B * 2 * x⁻¹ ^ 3 := by rw [hB]; ring
    linarith [hPre, h2]
  have hxP : x * P.re ≤ x * R + 1 / 32 := by
    rw [mul_add] at hmono; linarith
  have hG : (∑ d ∈ Finset.Icc 1 Nn, χ (d : ZMod q) * ((gExp ((d : ℝ) / x) : ℝ) : ℂ)).re ≤ B / 2 := by
    rw [hB]; exact hGre
  have hmain : 2 * B / (68 / 25 : ℝ) ≤ x * R + 1 / 32 + B / 2 + 1 / 1000 := by
    linarith [hs, hKe, hG, htail, h48, hxP]
  have hxR : B / 5 ≤ x * R := by linarith
  rw [hxB] at hxR
  have hB0 : 0 < B := by linarith
  have hfin : B * 1 ≤ B * (R * (20 * B)) := by linarith
  have := le_of_mul_le_mul_left hfin hB0
  rw [div_le_iff₀ (by positivity)]
  linarith

end Formalism.HermitianLattices.Ext.SupplyAP
