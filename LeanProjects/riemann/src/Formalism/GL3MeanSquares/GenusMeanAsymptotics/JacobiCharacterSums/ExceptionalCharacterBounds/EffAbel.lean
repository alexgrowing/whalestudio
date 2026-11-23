import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.ExceptionalCharacterBounds.EffBase
import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.LGrowth

noncomputable section

namespace Formalism.HermitianLattices.Ext.SupplyAP

theorem gExp_nonpos {t : ℝ} (ht : 0 < t) : gExp t ≤ 0 := by
  unfold gExp
  have h1 : t ≤ Real.exp t - 1 := by linarith [Real.add_one_le_exp t]
  have : 1 / (Real.exp t - 1) ≤ 1 / t := one_div_le_one_div_of_le ht h1
  linarith

private def hFun (t : ℝ) : ℝ := (2 + t) - (2 - t) * Real.exp t

private theorem hFun_hasDerivAt (t : ℝ) : HasDerivAt hFun (1 - (1 - t) * Real.exp t) t := by
  have h1 : HasDerivAt (fun t : ℝ => 2 + t) 1 t := (hasDerivAt_id t).const_add 2
  have h2 : HasDerivAt (fun t : ℝ => 2 - t) (-1) t := by
    simpa using (hasDerivAt_id t).const_sub 2
  have h3 := h2.mul (Real.hasDerivAt_exp t)
  have h4 := h1.sub h3
  exact h4.congr_deriv (by ring)

private theorem hFun_mono : Monotone hFun := by
  refine monotone_of_deriv_nonneg (fun t => (hFun_hasDerivAt t).differentiableAt) ?_
  intro t
  rw [(hFun_hasDerivAt t).deriv]
  have h1 : 1 - t ≤ Real.exp (-t) := by linarith [Real.add_one_le_exp (-t)]
  have h2 : Real.exp (-t) * Real.exp t = 1 := by rw [← Real.exp_add]; simp
  have h3 := mul_le_mul_of_nonneg_right h1 (Real.exp_pos t).le
  linarith

theorem neg_half_le_gExp {t : ℝ} (ht : 0 < t) : -(1 / 2) ≤ gExp t := by
  unfold gExp
  have hE : 0 < Real.exp t - 1 := by linarith [Real.add_one_le_exp t]
  have hh : hFun 0 ≤ hFun t := hFun_mono ht.le
  have h0 : hFun 0 = 0 := by simp [hFun]
  rw [h0] at hh
  unfold hFun at hh
  rw [div_sub_div _ _ hE.ne' ht.ne', le_div_iff₀ (mul_pos hE ht)]
  nlinarith

private theorem gExp_hasDerivAt {t : ℝ} (ht : 0 < t) :
    HasDerivAt gExp (-(Real.exp t) / (Real.exp t - 1) ^ 2 - (-(1 / t ^ 2))) t := by
  have hE : Real.exp t - 1 ≠ 0 := by linarith [Real.add_one_le_exp t]
  have h1 : HasDerivAt (fun t => 1 / (Real.exp t - 1)) (-(Real.exp t) / (Real.exp t - 1) ^ 2) t := by
    have := (hasDerivAt_const t (1:ℝ)).div ((Real.hasDerivAt_exp t).sub_const 1) hE
    exact this.congr_deriv (by ring)
  have h2 : HasDerivAt (fun t : ℝ => 1 / t) (-(1 / t ^ 2)) t := by
    have := (hasDerivAt_const t (1:ℝ)).div (hasDerivAt_id' t) ht.ne'
    exact this.congr_deriv (by ring)
  exact h1.sub h2

theorem gExp_monotoneOn : MonotoneOn gExp (Set.Ioi 0) := by
  refine monotoneOn_of_deriv_nonneg (convex_Ioi 0) ?_ ?_ ?_
  · intro t ht; exact (gExp_hasDerivAt ht).continuousAt.continuousWithinAt
  · intro t ht
    rw [interior_Ioi] at ht
    exact (gExp_hasDerivAt ht).differentiableAt.differentiableWithinAt
  · intro t ht
    rw [interior_Ioi] at ht
    have ht : 0 < t := ht
    rw [(gExp_hasDerivAt ht).deriv]
    have hE : 0 < Real.exp t - 1 := by linarith [Real.add_one_le_exp t]
    set a := Real.exp (t / 2)
    set b := Real.exp (-(t / 2))
    have hab : a * b = 1 := by simp only [a, b]; rw [← Real.exp_add]; simp
    have haa : a * a = Real.exp t := by simp only [a]; rw [← Real.exp_add]; ring_nf
    have hs : t / 2 ≤ Real.sinh (t / 2) := Real.self_le_sinh_iff.mpr (by linarith)
    rw [Real.sinh_eq] at hs
    have hd : t ≤ a - b := by linarith
    have ha : 0 < a := Real.exp_pos _
    have key : Real.exp t * t ^ 2 ≤ (Real.exp t - 1) ^ 2 := by
      rw [← haa, ← hab]
      have : t ^ 2 ≤ (a - b) ^ 2 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left this (mul_self_nonneg a)]
    have : Real.exp t / (Real.exp t - 1) ^ 2 ≤ 1 / t ^ 2 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]; linarith
    rw [neg_div]; linarith

open Finset in

theorem abelG (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (x : ℝ) (hx : 0 < x) (N : ℕ) :
    ‖∑ d ∈ Finset.Icc 1 N, χ (d : ZMod q) * ((gExp ((d : ℝ) / x) : ℝ) : ℂ)‖ ≤ ((q : ℝ) + 1) / 2 := by
  set b : ℕ → ℝ := fun d => gExp ((d : ℝ) / x) with hb
  set S : ℕ → ℂ := fun M => ∑ n ∈ Icc 1 M, χ (n : ZMod q) with hS
  set B : ℝ := (q : ℝ) + 1 with hB
  have hSB : ∀ M, ‖S M‖ ≤ B := fun M => Formalism.ZeroFreeDirichlet.norm_character_sum_Icc_le χ hχ M
  have hB0 : 0 ≤ B := by positivity
  have hpos : ∀ d : ℕ, 1 ≤ d → (0 : ℝ) < (d : ℝ) / x := fun d hd => by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    positivity
  have hmono : ∀ d : ℕ, 1 ≤ d → b d ≤ b (d + 1) := by
    intro d hd
    refine gExp_monotoneOn (hpos d hd) (hpos (d + 1) (by omega)) ?_
    push_cast
    exact div_le_div_of_nonneg_right (by linarith) hx.le
  have hle0 : ∀ d : ℕ, 1 ≤ d → b d ≤ 0 := fun d hd => gExp_nonpos (hpos d hd)
  have hhalf : -(1 / 2) ≤ b 1 := neg_half_le_gExp (hpos 1 le_rfl)
  set F : ℕ → ℂ := fun N => ∑ d ∈ Icc 1 N, χ (d : ZMod q) * ((b d : ℝ) : ℂ) with hF
  have hT : ∀ M : ℕ, ‖F (M + 1) - S (M + 1) * ((b (M + 1) : ℝ) : ℂ)‖ ≤ B * (b (M + 1) - b 1) := by
    intro M
    induction M with
    | zero => simp [hF, hS]
    | succ M ih =>
      have hF1 : F (M + 1 + 1) = F (M + 1) + χ ((M + 1 + 1 : ℕ) : ZMod q) * ((b (M + 1 + 1) : ℝ) : ℂ) := by
        simp only [hF]; rw [Finset.sum_Icc_succ_top (by omega)]
      have hS1 : S (M + 1 + 1) = S (M + 1) + χ ((M + 1 + 1 : ℕ) : ZMod q) := by
        simp only [hS]; rw [Finset.sum_Icc_succ_top (by omega)]
      have heq : F (M + 1 + 1) - S (M + 1 + 1) * ((b (M + 1 + 1) : ℝ) : ℂ) =
          (F (M + 1) - S (M + 1) * ((b (M + 1) : ℝ) : ℂ)) - S (M + 1) * ((b (M + 1 + 1) - b (M + 1) : ℝ) : ℂ) := by
        rw [hF1, hS1]; push_cast; ring
      rw [heq]
      have hd := hmono (M + 1) (by omega)
      calc _ ≤ ‖F (M + 1) - S (M + 1) * ((b (M + 1) : ℝ) : ℂ)‖ + ‖S (M + 1) * ((b (M + 1 + 1) - b (M + 1) : ℝ) : ℂ)‖ :=
            norm_sub_le _ _
        _ ≤ B * (b (M + 1) - b 1) + B * (b (M + 1 + 1) - b (M + 1)) := by
            gcongr
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
            exact mul_le_mul_of_nonneg_right (hSB _) (by linarith)
        _ = B * (b (M + 1 + 1) - b 1) := by ring
  change ‖F N‖ ≤ B / 2
  rcases N with _ | M
  · simp [hF]; positivity
  · have h1 := hT M
    have h2 : ‖S (M + 1) * ((b (M + 1) : ℝ) : ℂ)‖ ≤ B * (-b (M + 1)) := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (hle0 _ (by omega))]
      exact mul_le_mul_of_nonneg_right (hSB _) (by linarith [hle0 (M + 1) (by omega)])
    have h3 : F (M + 1) = (F (M + 1) - S (M + 1) * ((b (M + 1) : ℝ) : ℂ)) + S (M + 1) * ((b (M + 1) : ℝ) : ℂ) := by ring
    rw [h3]
    calc _ ≤ _ := norm_add_le _ _
      _ ≤ B * (b (M + 1) - b 1) + B * (-b (M + 1)) := add_le_add h1 h2
      _ = B * (-b 1) := by ring
      _ ≤ B / 2 := by nlinarith

end Formalism.HermitianLattices.Ext.SupplyAP
