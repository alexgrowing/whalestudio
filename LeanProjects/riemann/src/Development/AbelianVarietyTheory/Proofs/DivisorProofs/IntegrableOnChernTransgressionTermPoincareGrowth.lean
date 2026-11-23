import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EndValuedForm11Coeffs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtTransgressionTopCoeffComplexStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransgressionTopCoeffComplexEqZeroOfCutoffZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableOnOffCoordinateHyperplanesOfPoincareBoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormPolarisedTopChernCoeffLeOfWeightedBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoincareCoordinateLengthMemIccAndPosStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundFamilyOfIsCompact

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

theorem integrableOn_corrC : ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (S : Finset (Fin n)) (U K : Set (V n)) (G₀ G₁ : V n → Matrix r r ℂ) (ρ : V n → ℝ) (c : ℝ), IsOpen U → IsCompact K → K ⊆ U → (∀ v ∈ U, ∀ a ∈ S, ‖v a‖ ≤ 1 / 2) → (∀ v ∈ U, MContDiffAt ∞ G₀ v ∧ IsUnit (G₀ v).det) → (∀ v ∈ offHyp S U, MContDiffAt ∞ G₁ v ∧ IsUnit (G₁ v).det) → (∀ v ∈ offHyp S U, ∀ a i j, ‖conn G₁ v (coordVec a) i j‖ * poinWt S v a ≤ c) → (∀ v ∈ offHyp S U, ∀ a b i j, ‖curv G₁ v (coordVec a) (coordVec b) i j‖ * (poinWt S v a * poinWt S v b) ≤ c) → ContDiffOn ℝ ∞ ρ U → (∀ v ∈ U, v ∉ K → ρ v = 0) → IntegrableOn (corrC ρ G₀ G₁) (offHyp S U) := by
  intro n r _ _ S U K G₀ G₁ ρ c hU hK hKU hsmall hG₀ hG₁ hconn hcurv hρ hρK
  obtain ⟨C, hC0, hCb⟩ := exists_bound_smooth_data U K G₀ ρ hU hK hKU hG₀ hρ
  set c' : ℝ := |c| + C + C * (|c| + C) with hc'
  have hposition : ∀ v ∈ offHyp S U, v ∈ K → ∀ j : Fin n, ∀ i a b p q,
      ‖intersection_update_fsHerm_neg_one (curvAt G₁ v) (cutForm ρ G₀ G₁ v) (curvAt G₀ v) j i a b p q‖ *
        (poinWt S v a * poinWt S v b) ≤ c' := by
    intro v hv hvK j i a b p q
    obtain ⟨-, hdb, hcn, hcv⟩ := hCb v hvK
    have hw01 := (GlobalTheory.T.poincareCoordinateLength_mem_Icc_and_pos S v (hsmall v hv.1)).1
    have hwa := hw01 a
    have hwb := hw01 b
    have hab : poinWt S v a * poinWt S v b ≤ 1 := mul_le_one₀ hwa.2 hwb.1 hwb.2
    have hab0 : 0 ≤ poinWt S v a * poinWt S v b := mul_nonneg hwa.1 hwb.1
    have hca : 0 ≤ |c| := abs_nonneg c
    have hCc : 0 ≤ C * (|c| + C) := mul_nonneg hC0 (add_nonneg hca hC0)
    unfold intersection_update_fsHerm_neg_one
    split_ifs with h1 h2
    · have := hcurv v hv a b p q
      simp only [curvAt]
      linarith [le_abs_self c]
    · simp only [cutForm, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, norm_mul]
      have e1 := hconn v hv a p q
      have e2 := hcn a p q
      have e3 := hdb b
      have hxy := norm_sub_le (conn G₁ v (coordVec a) p q) (conn G₀ v (coordVec a) p q)
      have hD0 := norm_nonneg (dbar (fun x => (ρ x : ℂ)) v (coordVec b))
      have hN0 := norm_nonneg (conn G₁ v (coordVec a) p q - conn G₀ v (coordVec a) p q)
      have hwab : poinWt S v a * poinWt S v b ≤ poinWt S v a := mul_le_of_le_one_right hwa.1 hwb.2
      have hY : ‖conn G₀ v (coordVec a) p q‖ * poinWt S v a ≤ C :=
        (mul_le_mul e2 hwa.2 hwa.1 hC0).trans (by rw [mul_one])
      have hS : (‖conn G₁ v (coordVec a) p q - conn G₀ v (coordVec a) p q‖) * poinWt S v a ≤ |c| + C := by
        calc _ ≤ (‖conn G₁ v (coordVec a) p q‖ + ‖conn G₀ v (coordVec a) p q‖) * poinWt S v a :=
              mul_le_mul_of_nonneg_right hxy hwa.1
          _ ≤ |c| + C := by rw [add_mul]; linarith [le_abs_self c]
      calc _ ≤ ‖dbar (fun x => (ρ x : ℂ)) v (coordVec b)‖ *
              ‖conn G₁ v (coordVec a) p q - conn G₀ v (coordVec a) p q‖ * poinWt S v a :=
            mul_le_mul_of_nonneg_left hwab (mul_nonneg hD0 hN0)
        _ = ‖dbar (fun x => (ρ x : ℂ)) v (coordVec b)‖ *
              (‖conn G₁ v (coordVec a) p q - conn G₀ v (coordVec a) p q‖ * poinWt S v a) := by ring
        _ ≤ C * (|c| + C) := mul_le_mul e3 hS (mul_nonneg hN0 hwa.1) hC0
        _ ≤ c' := by linarith
    · have := hcv a b p q
      simp only [curvAt]
      have : ‖curv G₀ v (coordVec a) (coordVec b) p q‖ * (poinWt S v a * poinWt S v b) ≤ C :=
        (mul_le_mul this hab hab0 hC0).trans (by rw [mul_one])
      linarith
  refine GlobalTheory.T.integrableOn_offCoordinateHyperplanes_of_poincareBound S U K (corrC ρ G₀ G₁)
    ((n : ℝ) * ((Fintype.card r : ℝ) ^ n * (n.factorial : ℝ) ^ 2 * |c'| ^ n)) hU hK hKU hsmall ?_ ?_ ?_
  · intro v hv
    have hvU := hv.1
    have hρv : ContDiffAt ℝ 1 ρ v :=
      (hρ.contDiffAt (hU.mem_nhds hvU)).of_le (WithTop.coe_le_coe.2 le_top)
    exact (GlobalTheory.T.continuousAt_transgressionTopCoeffComplex hρv ((hG₀ v hvU).1.of_le (WithTop.coe_le_coe.2 le_top)) (hG₀ v hvU).2
      ((hG₁ v hv).1.of_le (WithTop.coe_le_coe.2 le_top)) (hG₁ v hv).2).continuousWithinAt
  · intro v hv hvK
    apply GlobalTheory.T.transgressionTopCoeffComplex_eq_zero_of_cutoff_zero
    have : U \ K ∈ 𝓝 v := (hU.sdiff hK.isClosed).mem_nhds ⟨hv.1, hvK⟩
    filter_upwards [this] with x hx
    exact hρK x hx.1 hx.2
  · intro v hv hvK
    have hwpos : ∀ a, 0 < poinWt S v a := (GlobalTheory.T.poincareCoordinateLength_mem_Icc_and_pos S v (hsmall v hv.1)).2 hv.2
    calc ‖corrC ρ G₀ G₁ v‖
        ≤ ∑ j : Fin n, ‖mixTop (intersection_update_fsHerm_neg_one (curvAt G₁ v) (cutForm ρ G₀ G₁ v) (curvAt G₀ v) j)‖ := norm_sum_le _ _
      _ ≤ ∑ _j : Fin n, (Fintype.card r : ℝ) ^ n * (n.factorial : ℝ) ^ 2 * |c'| ^ n *
            ∏ a, (poinWt S v a)⁻¹ ^ 2 :=
          Finset.sum_le_sum fun j _ => GlobalTheory.T.norm_polarisedTopChernCoeff_le_of_weighted_bound _ _ c' hwpos (hposition v hv hvK j)
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

end GlobalTheory.GoodTop
