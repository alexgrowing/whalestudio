import Formalism.SharpRestriction.CuspSpanNormBounds.MassRatioBound
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.EulerFacMulConjInvSplit

noncomputable section

namespace Formalism.MainNotions.BridgeLemVL

open NumberField Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.IdealNormInequalities

variable {K : Type} [Field K] [NumberField K] [StarRing K]

def Z2 : ℝ := ∑' n : ℕ, ((n : ℝ) ^ 2)⁻¹

theorem zeta_two_eq_pi_sq_div_six : Z2 = Real.pi ^ 2 / 6 := by
  unfold Z2
  rw [← hasSum_zeta_two.tsum_eq]
  congr 1
  ext n
  rw [one_div]

theorem sum_resChar_le (s : Finset {P : Ideal (𝓞 K) // P.IsMaximal}) :
    ∑ P ∈ s, ((resChar P.1 : ℝ) ^ 2)⁻¹ ≤ (Module.finrank ℚ K : ℝ) * Z2 := by
  classical
  have hs : Summable (fun n : ℕ => ((n : ℝ) ^ 2)⁻¹) := Real.summable_nat_pow_inv.mpr (by norm_num)
  have h1 : ∑ P ∈ s, ((resChar P.1 : ℝ) ^ 2)⁻¹ =
      ∑ n ∈ s.image (fun P => resChar P.1),
        ∑ P ∈ s.filter (fun P => resChar P.1 = n), ((resChar P.1 : ℝ) ^ 2)⁻¹ :=
    (Finset.sum_fiberwise_of_maps_to (fun P hP => Finset.mem_image_of_mem _ hP) _).symm
  rw [h1]
  calc ∑ n ∈ s.image (fun P => resChar P.1),
        ∑ P ∈ s.filter (fun P => resChar P.1 = n), ((resChar P.1 : ℝ) ^ 2)⁻¹
      ≤ ∑ n ∈ s.image (fun P => resChar P.1), (Module.finrank ℚ K : ℝ) * ((n : ℝ) ^ 2)⁻¹ := by
        refine Finset.sum_le_sum fun n _ => ?_
        have h2 : ∑ P ∈ s.filter (fun P => resChar P.1 = n), ((resChar P.1 : ℝ) ^ 2)⁻¹ =
            ((s.filter (fun P => resChar P.1 = n)).card : ℝ) * ((n : ℝ) ^ 2)⁻¹ := by
          rw [← nsmul_eq_mul, ← Finset.sum_const]
          refine Finset.sum_congr rfl fun P hP => ?_
          rw [(Finset.mem_filter.mp hP).2]
        rw [h2]
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        exact_mod_cast card_filter_resChar_le s n
    _ = (Module.finrank ℚ K : ℝ) * ∑ n ∈ s.image (fun P => resChar P.1), ((n : ℝ) ^ 2)⁻¹ := by
        rw [Finset.mul_sum]
    _ ≤ (Module.finrank ℚ K : ℝ) * Z2 := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact hs.sum_le_tsum _ (fun n _ => by positivity)

theorem eulerFac_two_le (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {P : Ideal (𝓞 K)} (hP : P.IsMaximal) :
    Formalism.HermitianLatticesTheory.eulerFac K 2 P ≤ Real.exp (2 * ((resChar P : ℝ) ^ 2)⁻¹) := by
  have hu := abs_smallTerm_le hK hP (le_refl 2)
  have hp : (2 : ℝ) ≤ (resChar P : ℝ) := by exact_mod_cast (resChar_prime hP).two_le
  have hq : ((resChar P : ℝ) ^ 2)⁻¹ ≤ 1 / 4 := by
    rw [inv_le_comm₀ (by positivity) (by norm_num)]
    nlinarith
  set u := smallTerm 2 P with hudef
  set y := ((resChar P : ℝ) ^ 2)⁻¹ with hy
  have hy0 : 0 ≤ y := by positivity
  have hua : |u| ≤ 1 / 2 := by linarith
  have hpos : 0 < 1 + u := by linarith [neg_abs_le u]
  have key : (1 + u)⁻¹ ≤ Real.exp (2 * y) := by
    have h1 : 0 < 1 - |u| := by linarith
    have h2 : (1 + u)⁻¹ ≤ (1 - |u|)⁻¹ := by
      apply inv_anti₀ h1
      linarith [neg_abs_le u]
    exact h2.trans ((Formalism.MainNotions.MassRatioZetaBound.inv_one_sub_le_exp (abs_nonneg u) hua).trans
      (Real.exp_le_exp.2 (by linarith)))
  rw [eulerFac_eq]
  split_ifs with hc
  · exact key
  · rcases le_or_gt 1 (1 + u) with h | h
    · calc (1 + u) ^ (-(1 : ℝ) / 2) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos h (by norm_num)
        _ ≤ Real.exp (2 * y) := Real.one_le_exp (by positivity)
    · calc (1 + u) ^ (-(1 : ℝ) / 2) ≤ (1 + u) ^ (-(1 : ℝ)) :=
            Real.rpow_le_rpow_of_exponent_ge hpos h.le (by norm_num)
        _ = (1 + u)⁻¹ := Real.rpow_neg_one _
        _ ≤ Real.exp (2 * y) := key

theorem lValEta_two_le (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) :
    Formalism.HermitianLatticesTheory.lValEta K 2 ≤ Real.exp (2 * ((Module.finrank ℚ K : ℝ) * Z2)) := by
  unfold Formalism.HermitianLatticesTheory.lValEta
  refine (multipliable_eulerFac hK 2 le_rfl).tprod_le_of_prod_le fun s => ?_
  calc ∏ P ∈ s, Formalism.HermitianLatticesTheory.eulerFac K 2 P.1
      ≤ ∏ P ∈ s, Real.exp (2 * ((resChar P.1 : ℝ) ^ 2)⁻¹) :=
        Finset.prod_le_prod (fun P _ => (eulerFac_pos hK P.2 2 (by norm_num)).le)
          (fun P _ => eulerFac_two_le hK P.2)
    _ = Real.exp (2 * ∑ P ∈ s, ((resChar P.1 : ℝ) ^ 2)⁻¹) := by
        rw [← Real.exp_sum, Finset.mul_sum]
    _ ≤ Real.exp (2 * ((Module.finrank ℚ K : ℝ) * Z2)) :=
        Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (sum_resChar_le s) (by norm_num))

theorem mass_ratio_rank_two_le (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) :
    Formalism.HermitianLatticesTheory.massRatioRightSide K 2 ≤ ((Formalism.HermitianLatticesTheory.vInv K / Real.pi) ^ 2) ^ Formalism.HermitianLatticesTheory.fDeg K *
      Real.exp (2 * ((Module.finrank ℚ K : ℝ) * Z2)) := by
  unfold Formalism.HermitianLatticesTheory.massRatioRightSide
  have hv : 0 ≤ Formalism.HermitianLatticesTheory.vInv K := by
    have := Formalism.MainNotions.MassRatioZetaBound.one_le_two_vInv (K := K); linarith
  have e1 : (((Nat.factorial (2 - 1) : ℕ) : ℝ) * (Formalism.HermitianLatticesTheory.vInv K / Real.pi) ^ 2) =
      (Formalism.HermitianLatticesTheory.vInv K / Real.pi) ^ 2 := by norm_num
  rw [e1]
  set a : ℝ := ((Formalism.HermitianLatticesTheory.vInv K / Real.pi) ^ 2) ^ Formalism.HermitianLatticesTheory.fDeg K with ha
  have ha0 : 0 ≤ a := by positivity
  have hb1 : 1 ≤ Real.sqrt ((2 * Formalism.HermitianLatticesTheory.vInv K) ^ Formalism.HermitianLatticesTheory.fDeg K) :=
    Real.one_le_sqrt.2 (one_le_pow₀ Formalism.MainNotions.MassRatioZetaBound.one_le_two_vInv)
  calc a / Real.sqrt ((2 * Formalism.HermitianLatticesTheory.vInv K) ^ Formalism.HermitianLatticesTheory.fDeg K) * Formalism.HermitianLatticesTheory.lValEta K 2
      ≤ a / Real.sqrt ((2 * Formalism.HermitianLatticesTheory.vInv K) ^ Formalism.HermitianLatticesTheory.fDeg K) *
          Real.exp (2 * ((Module.finrank ℚ K : ℝ) * Z2)) :=
        mul_le_mul_of_nonneg_left (lValEta_two_le hK) (div_nonneg ha0 (by linarith))
    _ ≤ a * Real.exp (2 * ((Module.finrank ℚ K : ℝ) * Z2)) :=
        mul_le_mul_of_nonneg_right (div_le_self ha0 hb1) (Real.exp_pos _).le

end Formalism.MainNotions.BridgeLemVL

end
