import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTDHHyperB

open Finset Complex Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.Hyp

variable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)

private theorem hH_eq_harmonic' (k : ℕ) : hH k = ((harmonic k : ℚ) : ℝ) := by
  unfold hH
  rw [harmonic_eq_sum_Icc,
    show Finset.Ioc 0 k = Finset.Icc 1 k by
      ext a
      simp only [Finset.mem_Ioc, Finset.mem_Icc]
      omega]
  push_cast
  rfl

theorem term_bound (N U b : ℕ) (hb : 1 ≤ b) (hbU : b ≤ U) (hUN : U * U ≤ N) :
    |hH (N / b) - (Real.log N + Real.eulerMascheroniConstant - Real.log b)| ≤ 2 * b / N := by
  have hbpos : 0 < b := by omega
  have hbb : b * b ≤ N := le_trans (Nat.mul_le_mul hbU hbU) hUN
  have hk1 : 1 ≤ N / b := by
    rw [Nat.le_div_iff_mul_le hbpos]
    nlinarith
  have hdm := Nat.div_add_mod N b
  have hml := Nat.mod_lt N hbpos
  have hkb : N / b * b ≤ N := Nat.div_mul_le_self N b
  have hNlt : N < (N / b + 1) * b := by nlinarith
  have hk0 : N / b ≠ 0 := by omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by nlinarith)
  have hkR : (1 : ℝ) ≤ ((N / b : ℕ) : ℝ) := by exact_mod_cast hk1
  have hbR : (1 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have hkbR : ((N / b : ℕ) : ℝ) * b ≤ N := by exact_mod_cast hkb
  have hNltR : (N : ℝ) < (((N / b : ℕ) : ℝ) + 1) * b := by exact_mod_cast hNlt
  have hHk : hH (N / b) = ((harmonic (N / b) : ℚ) : ℝ) := hH_eq_harmonic' (N / b)
  have hA1 := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' (N / b)
  have hA2 := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant (N / b)
  simp only [Real.eulerMascheroniSeq', Real.eulerMascheroniSeq, hk0, if_false] at hA1 hA2
  rw [← hHk] at hA1 hA2
  set K : ℝ := ((N / b : ℕ) : ℝ) with hK
  have hlog1 : Real.log (K + 1) - Real.log K ≤ 1 / K := by
    rw [← Real.log_div (by positivity) (by positivity), add_div, div_self (by positivity)]
    have h := Real.log_le_sub_one_of_pos (show 0 < 1 + 1 / K by positivity)
    linarith
  have hlogB1 : Real.log K + Real.log b - Real.log N ≤ 0 := by
    rw [← Real.log_mul (by positivity) (by positivity)]
    linarith [Real.log_le_log (by positivity) hkbR]
  have hlogB2 : -(1 / K) ≤ Real.log K + Real.log b - Real.log N := by
    have h1 : Real.log N < Real.log ((K + 1) * b) := Real.log_lt_log hN0 hNltR
    rw [Real.log_mul (by positivity) (by positivity)] at h1
    linarith
  have hfin : 1 / K ≤ 2 * b / N := by
    rw [le_div_iff₀ hN0, div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
    nlinarith
  rw [abs_le]
  constructor <;> linarith

theorem cF_main (hχ : χ ≠ 1) (N U : ℕ) (hU : 1 ≤ U) (hUN : U * U ≤ N) :
    ‖cF χ N - (((Real.log N + Real.eulerMascheroniConstant : ℝ) : ℂ) * cS χ U - cT χ U)‖ ≤
      2 * U / N + 8 * ((q : ℝ) + 1) * (1 + Real.log N) / U := by
  have hUle : U ≤ N := le_trans (Nat.le_mul_of_pos_left U (by omega)) hUN
  have hN : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hU0 : (0 : ℝ) < U := by exact_mod_cast hU
  rw [cF_split χ N U hUle]
  have hX : (((Real.log N + Real.eulerMascheroniConstant : ℝ) : ℂ) * cS χ U - cT χ U) =
      ∑ b ∈ Ioc 0 U, χ (b : ZMod q) / (b : ℂ) *
        (((Real.log N + Real.eulerMascheroniConstant - Real.log b : ℝ)) : ℂ) := by
    unfold cS cT
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    push_cast
    ring
  rw [hX]
  have hre : ∀ A B C : ℂ, A + B - C = (A - C) + B := fun A B C => by ring
  rw [hre, ← Finset.sum_sub_distrib]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · refine (norm_sum_le _ _).trans ?_
    calc ∑ b ∈ Ioc 0 U, ‖χ (b : ZMod q) / (b : ℂ) * (hH (N / b) : ℂ) - χ (b : ZMod q) / (b : ℂ) *
          (((Real.log N + Real.eulerMascheroniConstant - Real.log b : ℝ)) : ℂ)‖
        ≤ ∑ b ∈ Ioc 0 U, 2 / (N : ℝ) := by
          apply Finset.sum_le_sum
          intro b hb
          rw [Finset.mem_Ioc] at hb
          have hb0 : (0 : ℝ) < b := by exact_mod_cast hb.1
          rw [← mul_sub, norm_mul, norm_div, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
            Complex.norm_natCast]
          have h1 := term_bound N U b hb.1 hb.2 hUN
          have h2 : ‖χ (b : ZMod q)‖ ≤ 1 := DirichletCharacter.norm_le_one χ _
          calc ‖χ (b : ZMod q)‖ / b * |hH (N / b) - (Real.log N + Real.eulerMascheroniConstant - Real.log b)|
              ≤ 1 / b * (2 * b / N) := by gcongr
            _ = 2 / N := by field_simp
      _ = 2 * U / N := by simp; ring
  · have htail : ∀ a ∈ Ioc 0 N, ‖∑ b ∈ Ioc U (N / a), χ (b : ZMod q) / (b : ℂ)‖ ≤ 8 * ((q : ℝ) + 1) / U := by
      intro a ha
      by_cases hM : N / a ≤ U
      · rw [Finset.Ioc_eq_empty (by omega), Finset.sum_empty, norm_zero]
        positivity
      · push_neg at hM
        have hsplit : ∑ b ∈ Ioc U (N / a), χ (b : ZMod q) / (b : ℂ) = cS χ (N / a) - cS χ U := by
          unfold cS
          rw [← Finset.sum_Ioc_consecutive _ (Nat.zero_le U) hM.le]
          ring
        rw [hsplit]
        have h1 := cS_approx χ hχ U hU
        have h2 := cS_approx χ hχ (N / a) (by omega)
        have hMR : (U : ℝ) ≤ ((N / a : ℕ) : ℝ) := by exact_mod_cast hM.le
        have h3 : 4 * ((q : ℝ) + 1) / ((N / a : ℕ) : ℝ) ≤ 4 * ((q : ℝ) + 1) / U :=
          div_le_div_of_nonneg_left (by positivity) hU0 hMR
        calc ‖cS χ (N / a) - cS χ U‖ = ‖(DirichletCharacter.LFunction χ 1 - cS χ U) -
              (DirichletCharacter.LFunction χ 1 - cS χ (N / a))‖ := by
              congr 1
              ring
          _ ≤ ‖DirichletCharacter.LFunction χ 1 - cS χ U‖ +
              ‖DirichletCharacter.LFunction χ 1 - cS χ (N / a)‖ := norm_sub_le _ _
          _ ≤ 4 * ((q : ℝ) + 1) / U + 4 * ((q : ℝ) + 1) / U := add_le_add h1 (h2.trans h3)
          _ = 8 * ((q : ℝ) + 1) / U := by ring
    refine (norm_sum_le _ _).trans ?_
    calc ∑ a ∈ Ioc 0 N, ‖((a : ℂ))⁻¹ * ∑ b ∈ Ioc U (N / a), χ (b : ZMod q) / (b : ℂ)‖
        ≤ ∑ a ∈ Ioc 0 N, ((a : ℝ))⁻¹ * (8 * ((q : ℝ) + 1) / U) := by
          apply Finset.sum_le_sum
          intro a ha
          rw [norm_mul, norm_inv, Complex.norm_natCast]
          exact mul_le_mul_of_nonneg_left (htail a ha) (by positivity)
      _ = hH N * (8 * ((q : ℝ) + 1) / U) := by rw [hH, Finset.sum_mul]
      _ ≤ (1 + Real.log N) * (8 * ((q : ℝ) + 1) / U) := by
          have hh : hH N ≤ 1 + Real.log N := by
            rw [hH_eq_harmonic']
            exact harmonic_le_one_add_log N
          exact mul_le_mul_of_nonneg_right hh (by positivity)
      _ = 8 * ((q : ℝ) + 1) * (1 + Real.log N) / U := by ring

theorem cF_approx (hχ : χ ≠ 1) (N : ℕ) (hN : 1 ≤ N) :
    ‖cF χ N - (((Real.log N + Real.eulerMascheroniConstant : ℝ) : ℂ) *
        DirichletCharacter.LFunction χ 1 - cT χ (Nat.sqrt N))‖ ≤
      26 * ((q : ℝ) + 1) * (Real.log N + 1) / √(N : ℝ) := by
  have hU : 1 ≤ Nat.sqrt N := Nat.le_sqrt.2 (by omega)
  have hUN : Nat.sqrt N * Nat.sqrt N ≤ N := Nat.sqrt_le N
  have hlt : N < (Nat.sqrt N + 1) * (Nat.sqrt N + 1) := Nat.lt_succ_sqrt N
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hUR : (1 : ℝ) ≤ (Nat.sqrt N : ℝ) := by exact_mod_cast hU
  have hs0 : 0 < √(N : ℝ) := Real.sqrt_pos.2 hNR
  have hsq : √(N : ℝ) < (Nat.sqrt N : ℝ) + 1 := by
    have h := Real.sqrt_lt_sqrt (by positivity)
      (show (N : ℝ) < ((Nat.sqrt N : ℝ) + 1) * ((Nat.sqrt N : ℝ) + 1) by exact_mod_cast hlt)
    rwa [Real.sqrt_mul_self (by positivity)] at h
  have hsq2 : (Nat.sqrt N : ℝ) ≤ √(N : ℝ) := by
    have h := Real.sqrt_le_sqrt (show ((Nat.sqrt N : ℝ) * (Nat.sqrt N : ℝ)) ≤ N by exact_mod_cast hUN)
    rwa [Real.sqrt_mul_self (by positivity)] at h
  have hL0 : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  have hγ0 : 0 ≤ Real.eulerMascheroniConstant := by
    linarith [Real.one_half_lt_eulerMascheroniConstant]
  have hγ1 : Real.eulerMascheroniConstant ≤ 1 := by
    linarith [Real.eulerMascheroniConstant_lt_two_thirds]
  have hc : 0 ≤ Real.log N + Real.eulerMascheroniConstant := by linarith
  have h1 := cF_main χ hχ N (Nat.sqrt N) hU hUN
  have h2 := cS_approx χ hχ (Nat.sqrt N) hU
  have hdec : cF χ N - (((Real.log N + Real.eulerMascheroniConstant : ℝ) : ℂ) *
        DirichletCharacter.LFunction χ 1 - cT χ (Nat.sqrt N)) =
      (cF χ N - (((Real.log N + Real.eulerMascheroniConstant : ℝ) : ℂ) * cS χ (Nat.sqrt N) - cT χ (Nat.sqrt N))) +
        ((Real.log N + Real.eulerMascheroniConstant : ℝ) : ℂ) * (cS χ (Nat.sqrt N) - DirichletCharacter.LFunction χ 1) := by
    ring
  rw [hdec]
  have hw : 1 / (Nat.sqrt N : ℝ) ≤ 2 * (1 / √(N : ℝ)) := by
    have h := one_div_le_one_div_of_le hs0 (show √(N : ℝ) ≤ 2 * (Nat.sqrt N : ℝ) by linarith)
    calc 1 / (Nat.sqrt N : ℝ) = 2 * (1 / (2 * (Nat.sqrt N : ℝ))) := by field_simp
      _ ≤ 2 * (1 / √(N : ℝ)) := by linarith
  have hv : (Nat.sqrt N : ℝ) / N ≤ 1 / √(N : ℝ) := by
    calc (Nat.sqrt N : ℝ) / N = (Nat.sqrt N : ℝ) / (√(N : ℝ) * √(N : ℝ)) := by
          rw [Real.mul_self_sqrt hNR.le]
      _ ≤ √(N : ℝ) / (√(N : ℝ) * √(N : ℝ)) := by gcongr
      _ = 1 / √(N : ℝ) := by field_simp
  calc _ ≤ ‖cF χ N - (((Real.log N + Real.eulerMascheroniConstant : ℝ) : ℂ) * cS χ (Nat.sqrt N) -
          cT χ (Nat.sqrt N))‖ + ‖((Real.log N + Real.eulerMascheroniConstant : ℝ) : ℂ) *
          (cS χ (Nat.sqrt N) - DirichletCharacter.LFunction χ 1)‖ := norm_add_le _ _
    _ ≤ (2 * (Nat.sqrt N : ℝ) / N + 8 * ((q : ℝ) + 1) * (1 + Real.log N) / (Nat.sqrt N : ℝ)) +
          (Real.log N + Real.eulerMascheroniConstant) * (4 * ((q : ℝ) + 1) / (Nat.sqrt N : ℝ)) := by
        refine add_le_add h1 ?_
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hc, norm_sub_rev]
        exact mul_le_mul_of_nonneg_left h2 hc
    _ = 2 * ((Nat.sqrt N : ℝ) / N) + (8 * ((q : ℝ) + 1) * (1 + Real.log N) +
          4 * ((q : ℝ) + 1) * (Real.log N + Real.eulerMascheroniConstant)) * (1 / (Nat.sqrt N : ℝ)) := by
        ring
    _ ≤ 2 * (1 / √(N : ℝ)) + (8 * ((q : ℝ) + 1) * (1 + Real.log N) +
          4 * ((q : ℝ) + 1) * (Real.log N + Real.eulerMascheroniConstant)) * (2 * (1 / √(N : ℝ))) := by
        gcongr
    _ ≤ 26 * ((q : ℝ) + 1) * (Real.log N + 1) * (1 / √(N : ℝ)) := by
        have hZ : 0 ≤ 1 / √(N : ℝ) := by positivity
        have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
        have a3 : ((q : ℝ) + 1) * (1 / √(N : ℝ)) * Real.eulerMascheroniConstant ≤
            ((q : ℝ) + 1) * (1 / √(N : ℝ)) * 1 := mul_le_mul_of_nonneg_left hγ1 (by positivity)
        have a4 : 1 * (1 / √(N : ℝ)) ≤ ((q : ℝ) + 1) * (Real.log N + 1) * (1 / √(N : ℝ)) :=
          mul_le_mul_of_nonneg_right (by nlinarith) hZ
        nlinarith
    _ = 26 * ((q : ℝ) + 1) * (Real.log N + 1) / √(N : ℝ) := by ring

end Formalism.HermitianLattices.Ext.PrimesInProgressions.Hyp
