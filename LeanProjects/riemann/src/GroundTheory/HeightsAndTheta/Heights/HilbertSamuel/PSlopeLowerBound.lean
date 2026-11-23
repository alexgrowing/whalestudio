import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsHilbert
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsGenericFibre
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSectionsRank
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsDegreePositive
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter Asymptotics

noncomputable section

namespace SlopeLowerBound

theorem succ_rpow_isLittleO (D : ℕ) (hD : 1 ≤ D) :
    (fun n : ℕ => ((n : ℝ) + 1) ^ ((D : ℝ) - 1)) =o[atTop] fun n : ℕ => (n : ℝ) ^ D := by
  have hcast : (D : ℝ) - 1 = ((D - 1 : ℕ) : ℝ) := by rw [Nat.cast_sub hD, Nat.cast_one]
  have h1 : (fun n : ℕ => ((n : ℝ) + 1) ^ ((D : ℝ) - 1)) = fun n : ℕ => ((n : ℝ) + 1) ^ (D - 1) := by
    funext n; rw [hcast, Real.rpow_natCast]
  rw [h1]
  have hO : (fun n : ℕ => ((n : ℝ) + 1) ^ (D - 1)) =O[atTop] fun n : ℕ => (n : ℝ) ^ (D - 1) := by
    refine IsBigO.of_bound (2 ^ (D - 1)) ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity), abs_of_nonneg (by positivity),
      ← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by linarith) _
  exact hO.trans_isLittleO ((isLittleO_pow_pow_atTop_of_lt (𝕜 := ℝ) (show D - 1 < D by omega)).comp_tendsto
    tendsto_natCast_atTop_atTop)

theorem proof (hHSM : TheoremHSM.Statement) (hRank : RankOfSections.Statement)
    (hGen : GenericFibre.Statement) (hRk : SectionsRank.Statement) (hPos : DegreePositive.Statement) :
    SlopeLowerBound.Statement := by
  intro D Ω _ _ κ _ I d hI ε hε
  obtain ⟨hqP, hqd⟩ := hGen Ω κ d.x D d.arith
  obtain ⟨C, hC⟩ := hRank κ ((coordIdeal ℤ d.x).map (MvPolynomial.map (Int.castRingHom ℚ))) D hqP hqd
  have hδ0 := hPos ℚ κ ((coordIdeal ℤ d.x).map (MvPolynomial.map (Int.castRingHom ℚ))) D hqP hqd
  have hg : genDeg (ι := GlobalTheory κ) (coordIdeal ℤ d.x) D 1 =
      GroundTheory.Heights₂.Heights.NumbersDVR.intNum ℚ ((coordIdeal ℤ d.x).map (MvPolynomial.map (Int.castRingHom ℚ)))
        (fun _ : Fin D => fun _ => (1 : ℤ)) := by
    unfold genDeg
    convert rfl
    simp
  have hδ : (0 : ℝ) < (genDeg (ι := GlobalTheory κ) (coordIdeal ℤ d.x) D 1 : ℝ) := by rw [hg]; exact_mod_cast hδ0
  have hrank : ∀ n : ℕ, |(Module.finrank ℤ (sec ℤ d.x n) : ℝ) -
      (genDeg (ι := GlobalTheory κ) (coordIdeal ℤ d.x) D 1 : ℝ) * (n : ℝ) ^ D / D.factorial| ≤
        C * ((n : ℝ) + 1) ^ ((D : ℝ) - 1) := by
    intro n
    have e : (GroundTheory.Heights₂.Heights.NumbersDVR.hilbFn (ι := GlobalTheory κ)
        ((coordIdeal ℤ d.x).map (MvPolynomial.map (Int.castRingHom ℚ))) (fun _ => (n : ℤ)) : ℝ) =
        (Module.finrank ℤ (sec ℤ d.x n) : ℝ) := by exact_mod_cast hRk Ω κ d.x n
    rw [← e, hg]
    exact hC n
  set δ : ℝ := (genDeg (ι := GlobalTheory κ) (coordIdeal ℤ d.x) D 1 : ℝ) with hδdef
  set T : ℝ := top I d.x d.m D with hTdef
  set r : ℕ → ℝ := fun n => (Module.finrank ℤ (sec ℤ d.x n) : ℝ) with hrdef
  have hfD : (0 : ℝ) < D.factorial := by exact_mod_cast Nat.factorial_pos D
  have hfac : ((D + 1).factorial : ℝ) = ((D : ℝ) + 1) * D.factorial := by
    rw [Nat.factorial_succ]; push_cast; ring
  set c : ℝ := T / (((D : ℝ) + 1) * δ) with hcdef

  have hR : (fun n : ℕ => r n - δ * (n : ℝ) ^ D / D.factorial) =o[atTop] fun n : ℕ => (n : ℝ) ^ D := by
    refine IsBigO.trans_isLittleO ?_ (succ_rpow_isLittleO D d.one_le)
    refine IsBigO.of_bound C (Eventually.of_forall fun n => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
    exact hrank n

  have hH : (fun n : ℕ => resChi d n - T * (n : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)) =o[atTop] pw D :=
    (hHSM D Ω κ I d hI).1

  have hE : (fun n : ℕ => resChi d n - c * n * r n) =o[atTop] pw D := by
    have h2 : (fun n : ℕ => (c * (n : ℝ)) * (r n - δ * (n : ℝ) ^ D / D.factorial)) =o[atTop] pw D := by
      refine (((isBigO_refl (fun n : ℕ => (n : ℝ)) atTop).const_mul_left c).mul_isLittleO hR).congr
        (fun _ => rfl) ?_
      intro n; simp only [pw]; ring
    refine (hH.sub h2).congr (fun n => ?_) (fun _ => rfl)
    rw [hcdef, hfac]
    field_simp
    ring

  have hlow : ∀ᶠ n : ℕ in atTop, δ / (2 * D.factorial) * (n : ℝ) ^ D ≤ r n := by
    filter_upwards [hR.def (show 0 < δ / (2 * D.factorial) by positivity)] with n hn
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ D)] at hn
    have h1 := neg_abs_le (r n - δ * (n : ℝ) ^ D / D.factorial)
    have e : δ * (n : ℝ) ^ D / D.factorial = 2 * (δ / (2 * D.factorial) * (n : ℝ) ^ D) := by
      field_simp
    linarith
  filter_upwards [hlow, hE.def (show 0 < ε * (δ / (2 * D.factorial)) by positivity), eventually_ge_atTop 1]
    with n hn hEn hn1
  have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hrpos : 0 < r n := lt_of_lt_of_le (by positivity) hn
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ pw D n)] at hEn
  have hslope : T * n / (((D : ℝ) + 1) * δ) = c * n := by rw [hcdef]; ring
  show T * n / (((D : ℝ) + 1) * δ) - ε * n ≤ resChi d n / r n
  rw [hslope, le_div_iff₀ hrpos]
  have h1 : ε * n * (δ / (2 * D.factorial) * (n : ℝ) ^ D) ≤ ε * n * r n :=
    mul_le_mul_of_nonneg_left hn (by positivity)
  have h2 := neg_abs_le (resChi d n - c * n * r n)
  have h4 : ε * (δ / (2 * D.factorial)) * pw D n = ε * n * (δ / (2 * D.factorial) * (n : ℝ) ^ D) := by
    simp only [pw]; ring
  linarith

end SlopeLowerBound

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
