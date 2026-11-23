import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsProjDegGenDeg
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsHilbert
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenericFibre
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionsRank
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ChooseLePowDivFactorial
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Asymptotics

noncomputable section

namespace ProjDegGenDeg

theorem succ_rpow_isBigO (D : ℕ) :
    (fun n : ℕ => ((n : ℝ) + 1) ^ ((D : ℝ) - 1)) =O[atTop] fun n : ℕ => (n : ℝ) ^ D / (n : ℝ) := by
  refine IsBigO.of_bound (2 ^ D) ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hpos : (0 : ℝ) < n := by linarith
  rw [Real.rpow_sub_one (by positivity), Real.rpow_natCast, Real.norm_of_nonneg (by positivity),
    Real.norm_of_nonneg (by positivity)]
  calc ((n : ℝ) + 1) ^ D / ((n : ℝ) + 1) ≤ (2 * (n : ℝ)) ^ D / n :=
        div_le_div₀ (by positivity) (pow_le_pow_left₀ (by positivity) (by linarith) _) hpos (by linarith)
    _ = 2 ^ D * ((n : ℝ) ^ D / n) := by rw [mul_pow]; ring

theorem pow_div_isLittleO (D : ℕ) :
    (fun n : ℕ => (n : ℝ) ^ D / (n : ℝ)) =o[atTop] fun n : ℕ => (n : ℝ) ^ D := by
  have h1 : (fun n : ℕ => (1 : ℝ) / n) =o[atTop] fun _ : ℕ => (1 : ℝ) :=
    (isLittleO_one_iff ℝ).mpr tendsto_one_div_atTop_nhds_zero_nat
  exact (h1.mul_isBigO (isBigO_refl (fun n : ℕ => (n : ℝ) ^ D) atTop)).congr (fun n => by ring)
    (fun n => by ring)

theorem eq_zero_of_isBigO (D : ℕ) (c : ℝ)
    (h : (fun n : ℕ => c * (n : ℝ) ^ D) =O[atTop] fun n : ℕ => (n : ℝ) ^ D / (n : ℝ)) : c = 0 := by
  by_contra hc
  have h2 := (isLittleO_const_mul_left_iff hc).mp (h.trans_isLittleO (pow_div_isLittleO D))
  refine isLittleO_irrefl ?_ h2
  refine (eventually_ge_atTop 1).frequently.mono fun n hn => ?_
  have : (0 : ℝ) < n := by exact_mod_cast hn
  positivity

end ProjDegGenDeg

open ProjDegGenDeg in

theorem ProjDegGenDeg.proof (hR : RankOfSections.Statement) : ProjDegGenDeg.Statement := by
  intro D Ω _ _ κ _ x e hA hF
  obtain ⟨hq, hdim⟩ := GenericFibre.proof Ω κ x D hA
  obtain ⟨C, hC⟩ := hR κ _ D hq hdim
  set γ : ℤ := genDeg (ι := GlobalTheory κ) (coordIdeal ℤ x) D 1 with hγ
  have hγ' : GroundTheory.Heights₂.Heights.NumbersDVR.intNum ℚ
      ((coordIdeal ℤ x).map (MvPolynomial.map (Int.castRingHom ℚ)))
      (fun _ : Fin D => fun _ : Unit => (1 : ℤ)) = γ := by
    rw [hγ]; unfold genDeg; congr 1

  have h1 : (fun n : ℕ => (Module.finrank ℤ (sec ℤ x n) : ℝ) - (γ : ℝ) * (n : ℝ) ^ D / (D.factorial : ℝ))
      =O[atTop] fun n : ℕ => (n : ℝ) ^ D / (n : ℝ) := by
    refine IsBigO.trans ?_ (succ_rpow_isBigO D)
    refine IsBigO.of_bound C (Eventually.of_forall fun n => ?_)
    have hn := hC n
    rw [hγ', SectionsRank.proof Ω κ x n] at hn
    rw [Real.norm_eq_abs, Real.norm_of_nonneg (by positivity)]
    exact_mod_cast hn

  have h2 := finrank_sec_asymp x e hF
  have h3 : (fun n : ℕ => (((projDeg x e : ℝ) - (γ : ℝ)) / (D.factorial : ℝ)) * (n : ℝ) ^ D)
      =O[atTop] fun n : ℕ => (n : ℝ) ^ D / (n : ℝ) :=
    (h1.sub h2).congr_left fun n => by ring
  have h4 := eq_zero_of_isBigO D _ h3
  have hfac : (D.factorial : ℝ) ≠ 0 := by positivity
  rw [div_eq_zero_iff, sub_eq_zero] at h4
  rcases h4 with h4 | h4
  · exact_mod_cast h4.symm
  · exact absurd h4 hfac

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
