import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HsEighthLeOfSmall
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.FormalDegreeG2.ProdSubLtEqFactorial
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.FdScale
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.JacBound
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.PolarBasic
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.PBridge
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.IntegrableOfContinuousCompact
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.FdUpperA
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.FormalDegreeG2.FdUpperB
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.StdGap
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.AnyDec
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.DataGenSubIrred
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.HasGelfandCharSigLam

noncomputable section

open Finset Matrix MeasureTheory Filter Topology
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.G2

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

theorem fdU_s_pos {t : ℕ} (ht : 1 ≤ t) : 0 < (Real.sqrt (t : ℝ))⁻¹ := by
  exact inv_pos.mpr (Real.sqrt_pos.mpr (Nat.cast_pos.mpr ht))

theorem fdU_s_sq {t : ℕ} (ht : 1 ≤ t) : (Real.sqrt (t : ℝ))⁻¹ ^ 2 * t = 1 := by
  have ht0 : (t : ℝ) ≠ 0 := by
    have : (0 : ℝ) < t := by exact_mod_cast ht
    exact this.ne'
  rw [inv_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  exact inv_mul_cancel₀ ht0

theorem fdU_major {ε : Fin n → Bool} {lam : Fin n → ℝ} (hlam : Antitone lam) (t : ℕ)
    (ht : 16 * n * q0 ε + 1 ≤ t) (y : PCoord ε → ℂ) :
    ENNReal.ofReal (Real.exp (-2 * Ph (lamT lam t) (pmat ((((Real.sqrt t)⁻¹ : ℝ) : ℂ) • y))) *
        Jac ((((Real.sqrt t)⁻¹ : ℝ) : ℂ) • y)) ≤
      ENNReal.ofReal (Real.exp ((Real.sqrt ((16 * n * q0 ε + 1 : ℕ) : ℝ) / Real.sqrt (2 * (q0 ε : ℝ))) ^ 2 / 32) *
        ∏ ab : PCoord ε, Real.exp (-((Real.sqrt ((16 * n * q0 ε + 1 : ℕ) : ℝ) / Real.sqrt (2 * (q0 ε : ℝ)) / 8 -
          |(n : ℝ) - 1| * Real.sqrt (2 * (q0 ε : ℝ)) / Real.sqrt ((16 * n * q0 ε + 1 : ℕ) : ℝ)) /
            ((Fintype.card (PCoord ε) : ℝ) + 1)) * ‖y ab‖)) := by
  have h0 : 1 ≤ 16 * n * q0 ε + 1 := by omega
  have ht1 : 1 ≤ t := le_trans h0 ht
  have htpos : (0 : ℝ) < t := by exact_mod_cast ht1
  have hs0 : 0 < (Real.sqrt (t : ℝ))⁻¹ := inv_pos.mpr (Real.sqrt_pos.mpr htpos)
  have hst : (Real.sqrt (t : ℝ))⁻¹ ^ 2 * t = 1 := fdU_s_sq ht1
  have hfar := fdU_far hlam h0 ht hs0 hst y
  apply ENNReal.ofReal_le_ofReal
  refine hfar.trans ?_
  rw [sub_eq_add_neg, Real.exp_add]
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  rw [← neg_mul]
  by_cases hn : n = 0
  · have hE : IsEmpty (PCoord ε) := ⟨fun ab => by have := ab.1.1.2; omega⟩
    have hh : hs (pmat y) = 0 := by rw [hs_pmat]; simp
    rw [hh, Real.sqrt_zero, mul_zero, Real.exp_zero]
    simp
  · apply fdU_exp_le_prod
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
    have hm : |(n : ℝ) - 1| ≤ n := by rw [abs_of_nonneg (by linarith)]; linarith
    have hq : (0 : ℝ) ≤ q0 ε := Nat.cast_nonneg _
    have ha : 0 < Real.sqrt ((16 * n * q0 ε + 1 : ℕ) : ℝ) :=
      Real.sqrt_pos.mpr (by exact_mod_cast Nat.succ_pos _)
    have haa : Real.sqrt ((16 * n * q0 ε + 1 : ℕ) : ℝ) * Real.sqrt ((16 * n * q0 ε + 1 : ℕ) : ℝ) =
        16 * n * q0 ε + 1 := by
      rw [Real.mul_self_sqrt (Nat.cast_nonneg _)]; push_cast; ring
    rcases (Real.sqrt_nonneg (2 * (q0 ε : ℝ))).eq_or_lt with hb | hb
    · rw [← hb]; simp
    · have hbb : Real.sqrt (2 * (q0 ε : ℝ)) * Real.sqrt (2 * (q0 ε : ℝ)) = 2 * q0 ε :=
        Real.mul_self_sqrt (by positivity)
      rw [sub_nonneg, div_div, div_le_div_iff₀ ha (by positivity)]
      have key : |(n : ℝ) - 1| * (Real.sqrt (2 * (q0 ε : ℝ)) * Real.sqrt (2 * (q0 ε : ℝ))) * 8 ≤
          Real.sqrt ((16 * n * q0 ε + 1 : ℕ) : ℝ) * Real.sqrt ((16 * n * q0 ε + 1 : ℕ) : ℝ) := by
        rw [hbb, haa]; nlinarith
      nlinarith [key]

theorem fdU_pointwise {ε : Fin n → Bool} {lam : Fin n → ℝ} (hlam : Antitone lam) (T : ℕ) (hT : 1 ≤ T)
    (y : PCoord ε → ℂ) :
    limsup (fun t : ℕ => ENNReal.ofReal (Real.exp (-2 * Ph (lamT lam (t + T))
        (pmat ((((Real.sqrt ((t + T : ℕ) : ℝ))⁻¹ : ℝ) : ℂ) • y))) *
        Jac ((((Real.sqrt ((t + T : ℕ) : ℝ))⁻¹ : ℝ) : ℂ) • y))) atTop ≤
      ENNReal.ofReal (Real.exp (-Qf (0 : Fin n → ℝ) y)) := by
  have hs_tend : Filter.Tendsto (fun t : ℕ => (Real.sqrt ((t + T : ℕ) : ℝ))⁻¹) atTop (𝓝 0) := by
    have h1 : Filter.Tendsto (fun t : ℕ => ((t + T : ℕ) : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat T)
    exact tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp h1)
  have hc : Continuous (fun u : ℝ => ENNReal.ofReal (Real.exp (-(1 - u * rhoP y) * Qf (0 : Fin n → ℝ) y +
      ((n : ℝ) - 1) * Real.sqrt (2 * (q0 ε : ℝ)) * (u * Real.sqrt (hs (pmat y)))))) :=
    ENNReal.continuous_ofReal.comp (Real.continuous_exp.comp (by fun_prop))
  have hg := ((hc.tendsto 0).comp hs_tend).limsup_eq
  simp only [Function.comp_def] at hg
  have hev : ∀ᶠ t : ℕ in atTop, (Real.sqrt ((t + T : ℕ) : ℝ))⁻¹ * rhoP y ≤ 1 := by
    have h := hs_tend.mul_const (rhoP y)
    rw [zero_mul] at h
    exact h (Iic_mem_nhds one_pos)
  refine (Filter.limsup_le_limsup (v := fun t : ℕ => ENNReal.ofReal (Real.exp
      (-(1 - (Real.sqrt ((t + T : ℕ) : ℝ))⁻¹ * rhoP y) * Qf (0 : Fin n → ℝ) y +
        ((n : ℝ) - 1) * Real.sqrt (2 * (q0 ε : ℝ)) *
          ((Real.sqrt ((t + T : ℕ) : ℝ))⁻¹ * Real.sqrt (hs (pmat y))))))
      (hev.mono fun t ht => ?_)).trans (le_of_eq ?_)
  · have hT1 : 1 ≤ t + T := by omega
    have hpos : (0 : ℝ) < ((t + T : ℕ) : ℝ) := by exact_mod_cast hT1
    have hs0 : 0 < (Real.sqrt ((t + T : ℕ) : ℝ))⁻¹ := inv_pos.mpr (Real.sqrt_pos.mpr hpos)
    have hst := fdU_s_sq hT1
    have h := fdU_near hlam hs0 hst y ht
    exact ENNReal.ofReal_le_ofReal h
  · rw [hg]
    simp

theorem formal_degree_limsup_upper_bound {ε : Fin n → Bool} {lam : Fin n → ℝ} (hlam : Antitone lam) :
    Filter.limsup (fun t : ℕ => ENNReal.ofReal ((t : ℝ) ^ (pOf ε * qOf ε)) *
      ∫⁻ z : PCoord ε → ℂ, ENNReal.ofReal (Real.exp (-2 * Ph (lamT lam t) (pmat z)) * Jac z)) Filter.atTop ≤
      ENNReal.ofReal (PiW ε 0) := by
  have hscale : ∀ t : ℕ, 1 ≤ t → ENNReal.ofReal ((t : ℝ) ^ (pOf ε * qOf ε)) *
      ∫⁻ z : PCoord ε → ℂ, ENNReal.ofReal (Real.exp (-2 * Ph (lamT lam t) (pmat z)) * Jac z) =
      ∫⁻ y : PCoord ε → ℂ, ENNReal.ofReal (Real.exp (-2 * Ph (lamT lam t)
        (pmat ((((Real.sqrt t)⁻¹ : ℝ) : ℂ) • y))) * Jac ((((Real.sqrt t)⁻¹ : ℝ) : ℂ) • y)) := by
    intro t ht
    have htpos : (0 : ℝ) < t := by exact_mod_cast ht
    rw [lintegral_pcoord_smul _ (fdU_s_pos ht), ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
    have e : (t : ℝ) ^ (pOf ε * qOf ε) * ((Real.sqrt t)⁻¹) ^ (2 * (pOf ε * qOf ε)) = 1 := by
      rw [inv_pow, pow_mul (Real.sqrt (t : ℝ)) 2, Real.sq_sqrt htpos.le, mul_inv_cancel₀ (pow_ne_zero _ htpos.ne')]
    rw [e, ENNReal.ofReal_one, one_mul]
  set T : ℕ := 16 * n * q0 ε + 1 with hT
  rw [← Filter.limsup_nat_add _ T]
  refine le_trans (le_of_eq (Filter.limsup_congr (Filter.Eventually.of_forall fun i => hscale (i + T) (by omega)))) ?_
  have hmeas : ∀ t : ℕ, Measurable (fun y : PCoord ε → ℂ => ENNReal.ofReal (Real.exp (-2 * Ph (lamT lam (t + T))
      (pmat ((((Real.sqrt ((t + T : ℕ) : ℝ))⁻¹ : ℝ) : ℂ) • y))) *
        Jac ((((Real.sqrt ((t + T : ℕ) : ℝ))⁻¹ : ℝ) : ℂ) • y))) := by
    intro t
    apply ENNReal.measurable_ofReal.comp
    apply Continuous.measurable
    have hc : Continuous (fun y : PCoord ε → ℂ => (((Real.sqrt ((t + T : ℕ) : ℝ))⁻¹ : ℝ) : ℂ) • y) :=
      continuous_const_smul _
    exact (Real.continuous_exp.comp (continuous_const.mul ((continuous_potential_pmat _).comp hc))).mul
      ((jac_continuous ε).comp hc)
  have hint := ((fdU_integrable_prod_exp (ε := ε)
    (c := (Real.sqrt ((16 * n * q0 ε + 1 : ℕ) : ℝ) / Real.sqrt (2 * (q0 ε : ℝ)) / 8 -
          |(n : ℝ) - 1| * Real.sqrt (2 * (q0 ε : ℝ)) / Real.sqrt ((16 * n * q0 ε + 1 : ℕ) : ℝ)) /
            ((Fintype.card (PCoord ε) : ℝ) + 1))
    (fun ab => div_pos (fdU_c_pos ab) (by positivity))).const_mul
    (Real.exp ((Real.sqrt ((16 * n * q0 ε + 1 : ℕ) : ℝ) / Real.sqrt (2 * (q0 ε : ℝ))) ^ 2 / 32)))
  calc _ ≤ ∫⁻ y, limsup (fun t : ℕ => ENNReal.ofReal (Real.exp (-2 * Ph (lamT lam (t + T))
        (pmat ((((Real.sqrt ((t + T : ℕ) : ℝ))⁻¹ : ℝ) : ℂ) • y))) *
        Jac ((((Real.sqrt ((t + T : ℕ) : ℝ))⁻¹ : ℝ) : ℂ) • y))) atTop :=
        limsup_lintegral_le _ hmeas
          (fun t => Filter.Eventually.of_forall fun y => fdU_major hlam (t + T) (by omega) y)
          hint.lintegral_lt_top.ne
    _ ≤ ∫⁻ y, ENNReal.ofReal (Real.exp (-Qf (0 : Fin n → ℝ) y)) :=
        lintegral_mono fun y => fdU_pointwise hlam T (by omega) y
    _ = _ := fdU_lintegral_gauss ε

end ReciprocityTheory.ChartRestriction.DS.G2
