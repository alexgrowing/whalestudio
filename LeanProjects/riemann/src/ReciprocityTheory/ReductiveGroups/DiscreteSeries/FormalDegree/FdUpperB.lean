import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HsEighthLeOfSmall
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.ProdSubLtEqFactorial
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.JacBound
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.PBridge

noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

theorem fdU_hs_smul {ε : Fin n → Bool} (s : ℝ) (y : PCoord ε → ℂ) :
    hs (pmat ((s : ℂ) • y)) = s ^ 2 * hs (pmat y) := by
  have hp : pmat ((s : ℂ) • y) = (s : ℂ) • pmat y := by
    ext a b
    simp only [pmat, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul]
    split_ifs <;> simp [star_mul', Complex.conj_ofReal]
  rw [hp]
  unfold hs
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Matrix.smul_apply, smul_eq_mul, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]

theorem fdU_hs_nonneg {ε : Fin n → Bool} (y : PCoord ε → ℂ) : 0 ≤ hs (pmat y) := by
  unfold hs
  exact Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => by positivity))

theorem fdU_sqrt_hs_smul {ε : Fin n → Bool} {s : ℝ} (hs0 : 0 ≤ s) (y : PCoord ε → ℂ) :
    Real.sqrt (hs (pmat ((s : ℂ) • y))) = s * Real.sqrt (hs (pmat y)) := by
  rw [fdU_hs_smul, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hs0]

theorem fdU_qf_smul {ε : Fin n → Bool} (lam : Fin n → ℝ) (s : ℝ) (y : PCoord ε → ℂ) :
    Qf lam ((s : ℂ) • y) = s ^ 2 * Qf lam y := by
  unfold Qf
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun ab _ => ?_)
  rw [Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  ring

theorem fdU_antitone_zero : Antitone (0 : Fin n → ℝ) := fun _ _ _ => le_rfl

theorem fdU_ph_ge {ε : Fin n → Bool} {lam : Fin n → ℝ} (hlam : Antitone lam) (t : ℕ) (z : PCoord ε → ℂ) :
    (t : ℝ) * Ph (0 : Fin n → ℝ) (pmat z) ≤ Ph (lamT lam t) (pmat z) := by
  rw [ph_lamT]
  linarith [ph_nonneg hlam z]

theorem fdU_near {ε : Fin n → Bool} {lam : Fin n → ℝ} (hlam : Antitone lam) {s : ℝ} (hs0 : 0 < s) {t : ℕ}
    (hst : s ^ 2 * t = 1) (y : PCoord ε → ℂ) (hr : s * rhoP y ≤ 1) :
    Real.exp (-2 * Ph (lamT lam t) (pmat ((s : ℂ) • y))) * Jac ((s : ℂ) • y) ≤
      Real.exp (-(1 - s * rhoP y) * Qf (0 : Fin n → ℝ) y +
        ((n : ℝ) - 1) * Real.sqrt (2 * (q0 ε : ℝ)) * (s * Real.sqrt (hs (pmat y)))) := by
  have hrho : rhoP ((s : ℂ) • y) = s * rhoP y := by rw [rhoP_real_smul, abs_of_pos hs0]
  have hl := ph_lower (lam := (0 : Fin n → ℝ)) fdU_antitone_zero ((s : ℂ) • y) (ep := s * rhoP y) hrho.le hr
  rw [fdU_qf_smul] at hl
  have hg := fdU_ph_ge hlam t ((s : ℂ) • y)
  have ht : (0 : ℝ) ≤ t := Nat.cast_nonneg t
  have hQ : (1 - s * rhoP y) * Qf (0 : Fin n → ℝ) y =
      (t : ℝ) * ((1 - s * rhoP y) * (s ^ 2 * Qf (0 : Fin n → ℝ) y)) := by
    calc _ = (s ^ 2 * t) * ((1 - s * rhoP y) * Qf (0 : Fin n → ℝ) y) := by rw [hst]; ring
      _ = _ := by ring
  have hm := mul_le_mul_of_nonneg_left hl ht
  have h1 : (1 - s * rhoP y) * Qf (0 : Fin n → ℝ) y ≤ 2 * Ph (lamT lam t) (pmat ((s : ℂ) • y)) := by
    rw [hQ]; linarith
  have hJ := jac_le_exp ((s : ℂ) • y)
  rw [fdU_sqrt_hs_smul hs0.le] at hJ
  rw [Real.exp_add]
  exact mul_le_mul (Real.exp_le_exp.mpr (by linarith)) hJ (le_trans zero_le_one (jac_ge_one _))
    (Real.exp_pos _).le

theorem fdU_far {ε : Fin n → Bool} {lam : Fin n → ℝ} (hlam : Antitone lam) {t₀ t : ℕ} (h0 : 1 ≤ t₀)
    (ht : t₀ ≤ t) {s : ℝ} (hs0 : 0 < s) (hst : s ^ 2 * t = 1) (y : PCoord ε → ℂ) :
    Real.exp (-2 * Ph (lamT lam t) (pmat ((s : ℂ) • y))) * Jac ((s : ℂ) • y) ≤
      Real.exp ((Real.sqrt t₀ / Real.sqrt (2 * (q0 ε : ℝ))) ^ 2 / 32 -
        (Real.sqrt t₀ / Real.sqrt (2 * (q0 ε : ℝ)) / 8 -
          |(n : ℝ) - 1| * Real.sqrt (2 * (q0 ε : ℝ)) / Real.sqrt t₀) * Real.sqrt (hs (pmat y))) := by
  have hhs : hs (pmat y) = Real.sqrt (hs (pmat y)) ^ 2 := (Real.sq_sqrt (fdU_hs_nonneg y)).symm
  have hm := potential_lower_min ((s : ℂ) • y)
  rw [fdU_sqrt_hs_smul hs0.le, fdU_hs_smul] at hm
  have hJ := jac_le_exp ((s : ℂ) • y)
  rw [fdU_sqrt_hs_smul hs0.le] at hJ
  have hPh := fdU_ph_ge hlam t ((s : ℂ) • y)
  set k := Real.sqrt (2 * (q0 ε : ℝ)) with hk
  set r := Real.sqrt (hs (pmat y)) with hr
  set X := Real.sqrt (t₀ : ℝ) with hX
  set a := X / k with ha
  have hk0 : 0 ≤ k := Real.sqrt_nonneg _
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hT0 : 0 < X := Real.sqrt_pos.mpr (by exact_mod_cast h0)
  have ht0 : (0 : ℝ) ≤ t := Nat.cast_nonneg _
  have hsT : s * X ≤ 1 := by
    have h1 : s ^ 2 * t₀ ≤ 1 := by
      rw [← hst]; exact mul_le_mul_of_nonneg_left (by exact_mod_cast ht) (sq_nonneg s)
    have h2 : (s * X) ^ 2 ≤ 1 := by rw [mul_pow, hX, Real.sq_sqrt (Nat.cast_nonneg _)]; exact h1
    nlinarith [mul_pos hs0 hT0]
  have hsinv : X ≤ s⁻¹ := by
    calc X = s⁻¹ * (s * X) := by field_simp
      _ ≤ s⁻¹ * 1 := mul_le_mul_of_nonneg_left hsT (inv_nonneg.mpr hs0.le)
      _ = s⁻¹ := mul_one _
  have hmin : a * r - a ^ 2 / 4 ≤ (t : ℝ) * min (s ^ 2 * hs (pmat y)) (s * r / k) := by
    rw [mul_min_of_nonneg _ _ ht0]
    refine le_min ?_ ?_
    · have e : (t : ℝ) * (s ^ 2 * hs (pmat y)) = r ^ 2 := by
        rw [hhs]; linear_combination r ^ 2 * hst
      rw [e]; nlinarith [sq_nonneg (r - a / 2)]
    · have hrk : 0 ≤ r / k := div_nonneg hr0 hk0
      have e : (t : ℝ) * (s * r / k) = s⁻¹ * (r / k) := by
        have : s⁻¹ = s * t := by field_simp; linear_combination -hst
        rw [this]; ring
      have ea : a * r = X * (r / k) := by rw [ha]; ring
      rw [e]; nlinarith [mul_le_mul_of_nonneg_right hsinv hrk, sq_nonneg a]
  have hs' : s ≤ 1 / X := by rw [le_div_iff₀ hT0]; exact hsT
  have hJ2 : ((n : ℝ) - 1) * k * (s * r) ≤ |(n : ℝ) - 1| * k / X * r := by
    calc ((n : ℝ) - 1) * k * (s * r) ≤ |(n : ℝ) - 1| * k * (s * r) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) hk0) (by positivity)
      _ ≤ |(n : ℝ) - 1| * k * (1 / X * r) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hs' hr0) (by positivity)
      _ = _ := by ring
  have hm2 := mul_le_mul_of_nonneg_left hm ht0
  have hE : -2 * Ph (lamT lam t) (pmat ((s : ℂ) • y)) ≤ a ^ 2 / 32 - a / 8 * r := by
    nlinarith
  calc Real.exp (-2 * Ph (lamT lam t) (pmat ((s : ℂ) • y))) * Jac ((s : ℂ) • y)
      ≤ Real.exp (a ^ 2 / 32 - a / 8 * r) * Real.exp (|(n : ℝ) - 1| * k / X * r) :=
        mul_le_mul (Real.exp_le_exp.mpr hE) (hJ.trans (Real.exp_le_exp.mpr hJ2))
          (le_trans zero_le_one (jac_ge_one _)) (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem one_le_q0_of_coord {ε : Fin n → Bool} (ab : PCoord ε) : 1 ≤ q0 ε := by
  unfold q0 pOf qOf
  have h := ab.2.2
  have ht : ε ab.1.1 = true ∨ ε ab.1.2 = true := by
    cases h1 : ε ab.1.1 <;> cases h2 : ε ab.1.2 <;> simp_all
  have hf : ε ab.1.1 = false ∨ ε ab.1.2 = false := by
    cases h1 : ε ab.1.1 <;> cases h2 : ε ab.1.2 <;> simp_all
  apply le_min
  · rcases ht with h1 | h1
    · exact Finset.card_pos.mpr ⟨_, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1⟩⟩
    · exact Finset.card_pos.mpr ⟨_, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1⟩⟩
  · rcases hf with h1 | h1
    · exact Finset.card_pos.mpr ⟨_, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1⟩⟩
    · exact Finset.card_pos.mpr ⟨_, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1⟩⟩

theorem fdU_c_pos {ε : Fin n → Bool} (ab : PCoord ε) :
    0 < Real.sqrt ((16 * n * q0 ε + 1 : ℕ) : ℝ) / Real.sqrt (2 * (q0 ε : ℝ)) / 8 -
      |(n : ℝ) - 1| * Real.sqrt (2 * (q0 ε : ℝ)) / Real.sqrt ((16 * n * q0 ε + 1 : ℕ) : ℝ) := by
  have hQ : (1 : ℝ) ≤ q0 ε := by exact_mod_cast one_le_q0_of_coord ab
  have hn : (1 : ℝ) ≤ n := by
    have := ab.1.1.isLt
    exact_mod_cast (show 1 ≤ n by omega)
  have hA : (((16 * n * q0 ε + 1 : ℕ) : ℝ)) = 16 * n * q0 ε + 1 := by push_cast; ring
  rw [hA, abs_of_nonneg (by linarith : (0 : ℝ) ≤ n - 1)]
  have ha : 0 < Real.sqrt (16 * n * q0 ε + 1) := Real.sqrt_pos.mpr (by positivity)
  have hb : 0 < Real.sqrt (2 * (q0 ε : ℝ)) := Real.sqrt_pos.mpr (by positivity)
  have ha2 : Real.sqrt (16 * n * q0 ε + 1) ^ 2 = 16 * n * q0 ε + 1 := Real.sq_sqrt (by positivity)
  have hb2 : Real.sqrt (2 * (q0 ε : ℝ)) ^ 2 = 2 * q0 ε := Real.sq_sqrt (by positivity)
  have key : Real.sqrt (16 * n * q0 ε + 1) / Real.sqrt (2 * (q0 ε : ℝ)) / 8 -
      ((n : ℝ) - 1) * Real.sqrt (2 * (q0 ε : ℝ)) / Real.sqrt (16 * n * q0 ε + 1) =
      (Real.sqrt (16 * n * q0 ε + 1) ^ 2 - 8 * ((n : ℝ) - 1) * Real.sqrt (2 * (q0 ε : ℝ)) ^ 2) /
        (8 * Real.sqrt (16 * n * q0 ε + 1) * Real.sqrt (2 * (q0 ε : ℝ))) := by
    field_simp
  rw [key, ha2, hb2]
  apply div_pos _ (by positivity)
  nlinarith

theorem fdU_exp_le_prod {ε : Fin n → Bool} {c : ℝ} (hc : 0 ≤ c) (y : PCoord ε → ℂ) :
    Real.exp (-c * Real.sqrt (hs (pmat y))) ≤
      ∏ ab : PCoord ε, Real.exp (-(c / ((Fintype.card (PCoord ε) : ℝ) + 1)) * ‖y ab‖) := by
  rw [show (∏ ab : PCoord ε, Real.exp (-(c / ((Fintype.card (PCoord ε) : ℝ) + 1)) * ‖y ab‖)) =
      Real.exp (∑ ab : PCoord ε, -(c / ((Fintype.card (PCoord ε) : ℝ) + 1)) * ‖y ab‖) from
      (Real.exp_sum _ _).symm, Real.exp_le_exp]
  have hent : ∀ ab : PCoord ε, ‖y ab‖ ≤ Real.sqrt (hs (pmat y)) := by
    intro ab
    have hpm : pmat y ab.1.1 ab.1.2 = y ab := by
      simp only [pmat]
      rw [dif_pos ab.2]
    have h2 : ‖y ab‖ ^ 2 ≤ hs (pmat y) := by
      unfold hs
      calc ‖y ab‖ ^ 2 = ‖pmat y ab.1.1 ab.1.2‖ ^ 2 := by rw [hpm]
        _ ≤ ∑ j, ‖pmat y ab.1.1 j‖ ^ 2 :=
          Finset.single_le_sum (f := fun j => ‖pmat y ab.1.1 j‖ ^ 2) (fun _ _ => by positivity)
            (Finset.mem_univ _)
        _ ≤ ∑ i, ∑ j, ‖pmat y i j‖ ^ 2 :=
          Finset.single_le_sum (f := fun i => ∑ j, ‖pmat y i j‖ ^ 2)
            (fun _ _ => Finset.sum_nonneg (fun _ _ => by positivity)) (Finset.mem_univ _)
    calc ‖y ab‖ = |‖y ab‖| := (abs_of_nonneg (norm_nonneg _)).symm
      _ ≤ Real.sqrt (hs (pmat y)) := Real.abs_le_sqrt h2
  have hsq := Real.sqrt_nonneg (hs (pmat y))
  have hsum : ∑ ab : PCoord ε, ‖y ab‖ ≤ ((Fintype.card (PCoord ε) : ℝ) + 1) * Real.sqrt (hs (pmat y)) := by
    calc ∑ ab : PCoord ε, ‖y ab‖ ≤ ∑ ab : PCoord ε, Real.sqrt (hs (pmat y)) :=
          Finset.sum_le_sum (fun ab _ => hent ab)
      _ = (Fintype.card (PCoord ε) : ℝ) * Real.sqrt (hs (pmat y)) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ ≤ ((Fintype.card (PCoord ε) : ℝ) + 1) * Real.sqrt (hs (pmat y)) := by linarith
  rw [← Finset.mul_sum]
  have hN : (0 : ℝ) < (Fintype.card (PCoord ε) : ℝ) + 1 := by positivity
  have h3 := mul_le_mul_of_nonneg_left hsum (div_nonneg hc hN.le)
  have e : c / ((Fintype.card (PCoord ε) : ℝ) + 1) *
      (((Fintype.card (PCoord ε) : ℝ) + 1) * Real.sqrt (hs (pmat y))) = c * Real.sqrt (hs (pmat y)) := by
    field_simp
  linarith

end ReciprocityTheory.ChartRestriction.DS
