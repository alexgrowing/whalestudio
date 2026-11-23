import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcRealPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocalJacobianOfDoubleCoset

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL

open Formalism.L2.SG.RealObj CoordinateScalingProducts

theorem coordW_exact (r k : ℕ) (T T' sc : ℝ) (hk : 1 ≤ k) (hT : 0 < T) (hT' : 0 < T') (hsc : 0 < sc)
    (F : (Fin (r + 1) → ℂ) → ℝ≥0∞) :
    ∫⁻ q : (Fin r → ℂ) × ℂ, ENNReal.ofReal (Formalism.QuantumDeterminants.bcWeight k r T T' q) * F (coordSc r sc q) =
      ENNReal.ofReal ((2 ^ (r + 1) * nrm r sc * lamW r k sc)⁻¹) *
        ∫⁻ c in GoodLoc (r := r) T T', ENNReal.ofReal (wtLoc k T T' c) * F c ∂(dcLoc (r := r)) := by
  have hlam0 : ∀ a, lam r sc a ≠ 0 := lam_ne hsc
  have hΛ0 : 0 < lamW r k sc := Finset.prod_pos fun a _ => pow_pos (norm_pos_iff.2 (hlam0 a)) _
  have hN0 : 0 < nrm r sc := Complex.normSq_pos.2 (Finset.prod_ne_zero_iff.2 fun a _ => hlam0 a)
  have hpos : 0 < 2 ^ (r + 1) * nrm r sc * lamW r k sc := mul_pos (mul_pos (by positivity) hN0) hΛ0

  have hDl : ∀ l, Continuous fun c : Fin (r + 1) → ℂ => Dl (Matrix.diagonal c) l := by
    intro l
    by_cases hl : l ≤ r + 1
    · have e : (fun c : Fin (r + 1) → ℂ => Dl (Matrix.diagonal c) l) = fun c => ∏ i : Fin l, c (Fin.castLE hl i) :=
        funext fun c => dl_diag c l hl
      rw [e]; fun_prop
    · have e : (fun c : Fin (r + 1) → ℂ => Dl (Matrix.diagonal c) l) = fun _ => 0 :=
        funext fun c => by simp [Dl, hl]
      rw [e]; exact continuous_const
  have hGv : Continuous fun c : Fin (r + 1) → ℂ => Gv T T' (Matrix.diagonal c) := by
    simp only [Gv]
    exact ((hDl (r + 1)).norm.pow 2).sub (continuous_const.mul ((hDl r).norm.pow 2))
  have hGood : MeasurableSet (GoodLoc (r := r) T T') := by
    have e : GoodLoc (r := r) T T' =
        (⋂ l, {c : Fin (r + 1) → ℂ | c l ≠ 0}) ∩ {c | 0 < Gv T T' (Matrix.diagonal c)} := by
      ext c; simp [GoodLoc]
    rw [e]
    exact ((isOpen_iInter_of_finite fun l => isOpen_ne_fun (continuous_apply l) continuous_const).inter
      (isOpen_lt continuous_const hGv)).measurableSet

  have hptq : ∀ q : (Fin r → ℂ) × ℂ, Complex.normSq q.2 ≠ T * T' →
      Gi r k T T' F (coordSc r sc q) =
        ENNReal.ofReal (lamW r k sc) * (ENNReal.ofReal (Formalism.QuantumDeterminants.bcWeight k r T T' q) * F (coordSc r sc q)) := by
    intro q hq
    have hw := wt_cs hk T T' sc q
    have hg := gv_cs T T' sc q
    by_cases hq0 : ∀ a, q.1 a ≠ 0
    · by_cases hz : T * T' < Complex.normSq q.2
      · have hmem : coordSc r sc q ∈ GoodLoc (r := r) T T' := by
          refine ⟨fun l => ?_, ?_⟩
          · refine Fin.lastCases ?_ (fun a => ?_) l
            · rw [coordSc_last]
              intro h0
              rw [h0, map_zero] at hz
              exact absurd hz (not_lt.2 (mul_pos hT hT').le)
            · rw [coordSc_cs]; exact mul_ne_zero (hlam0 a) (hq0 a)
          · rw [hg]
            exact mul_pos (Finset.prod_pos fun a _ => pow_pos (norm_pos_iff.2 (mul_ne_zero (hlam0 a) (hq0 a))) 2)
              (by linarith)
        rw [Gi, Set.indicator_of_mem hmem, hw, Formalism.QuantumDeterminants.bcWeight, if_pos hz.le, ENNReal.ofReal_mul hΛ0.le, mul_assoc]
      · have hlt : Complex.normSq q.2 < T * T' := lt_of_le_of_ne (not_lt.1 hz) hq
        have hnot : coordSc r sc q ∉ GoodLoc (r := r) T T' := by
          rintro ⟨-, hp⟩
          rw [hg] at hp
          exact absurd hp (not_lt.2 (mul_nonpos_of_nonneg_of_nonpos
            (Finset.prod_nonneg fun a _ => by positivity) (sub_neg.2 hlt).le))
        rw [Gi, Set.indicator_apply_eq_zero.2 (fun h => absurd h hnot), Formalism.QuantumDeterminants.bcWeight,
          if_neg (not_le.2 hlt), ENNReal.ofReal_zero, zero_mul, mul_zero]
    · push_neg at hq0
      obtain ⟨a, ha⟩ := hq0
      have hnot : coordSc r sc q ∉ GoodLoc (r := r) T T' := by
        rintro ⟨hne, -⟩
        exact hne a.castSucc (by rw [coordSc_cs, ha, mul_zero])
      have hp : ∏ a : Fin r, ‖q.1 a‖ ^ (2 * (Formalism.QuantumDeterminants.Mdim k r a - 2)) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ a) (by
          rw [ha, norm_zero]
          exact zero_pow (by have := a.isLt; unfold Formalism.QuantumDeterminants.Mdim; omega))
      have hb : Formalism.QuantumDeterminants.bcWeight k r T T' q = 0 := by
        unfold Formalism.QuantumDeterminants.bcWeight; split_ifs <;> simp [hp]
      rw [Gi, Set.indicator_apply_eq_zero.2 (fun h => absurd h hnot), hb, ENNReal.ofReal_zero, zero_mul, mul_zero]

  have hnull : ∀ᵐ c : Fin (r + 1) → ℂ, Complex.normSq (c (Fin.last r)) ≠ T * T' := by
    have hS : (volume : Measure ℂ) {ζ | Complex.normSq ζ = T * T'} = 0 := by
      refine measure_mono_null (fun ζ hζ => ?_) (Measure.addHaar_sphere volume (0 : ℂ) (Real.sqrt (T * T')))
      simp only [Set.mem_setOf_eq] at hζ
      rw [mem_sphere_zero_iff_norm, ← hζ, Complex.normSq_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]
    have h0 : (volume : Measure (Fin (r + 1) → ℂ)) {c | Complex.normSq (c (Fin.last r)) = T * T'} = 0 := by
      exact Measure.pi_eval_preimage_null (fun _ : Fin (r + 1) => (volume : Measure ℂ)) (i := Fin.last r) hS
    exact ae_iff.2 (by simpa using h0)
  have hpt : ∀ᵐ c : Fin (r + 1) → ℂ, Gi r k T T' F c = ENNReal.ofReal (lamW r k sc) *
      (ENNReal.ofReal (Formalism.QuantumDeterminants.bcWeight k r T T' ((Phe r sc hsc).symm c)) * F c) := by
    filter_upwards [hnull] with c hc
    have hc' : coordSc r sc ((Phe r sc hsc).symm c) = c := by
      rw [← phe_apply hsc, MeasurableEquiv.apply_symm_apply]
    have h2 : ((Phe r sc hsc).symm c).2 = c (Fin.last r) := by
      conv_rhs => rw [← hc']
      rw [coordSc_last]
    have key := hptq ((Phe r sc hsc).symm c) (by rw [h2]; exact hc)
    rw [hc'] at key
    exact key

  have hL : ∫⁻ q : (Fin r → ℂ) × ℂ, ENNReal.ofReal (Formalism.QuantumDeterminants.bcWeight k r T T' q) * F (coordSc r sc q) =
      ENNReal.ofReal (nrm r sc)⁻¹ * ∫⁻ c : Fin (r + 1) → ℂ,
        ENNReal.ofReal (Formalism.QuantumDeterminants.bcWeight k r T T' ((Phe r sc hsc).symm c)) * F c := by
    rw [← smul_eq_mul, ← lintegral_smul_measure, ← map_Phe hsc, lintegral_map_equiv]
    refine lintegral_congr fun q => ?_
    rw [MeasurableEquiv.symm_apply_apply, phe_apply]
  rw [hL, show (∫⁻ c in GoodLoc (r := r) T T', ENNReal.ofReal (wtLoc k T T' c) * F c ∂(dcLoc (r := r))) =
      ∫⁻ c, Gi r k T T' F c ∂(dcLoc (r := r)) from (lintegral_indicator hGood _).symm,
    dcLoc_eq, lintegral_smul_measure, smul_eq_mul, lintegral_congr_ae hpt,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← mul_assoc, ← mul_assoc]
  congr 1
  rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_pow (by norm_num), ← ENNReal.ofReal_mul (inv_pos.2 hpos).le,
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  field_simp

theorem lam_one (r : ℕ) (a : Fin r) : lam r 1 a = 1 := by simp [lam]

theorem nrm_one (r : ℕ) : nrm r 1 = 1 := by simp [nrm, lam_one]

theorem lamW_one (r k : ℕ) : lamW r k 1 = 1 := by simp [lamW, lam_one]

theorem coordinate_weight_lintegral (r k : ℕ) (T T' : ℝ) (hk : 1 ≤ k) (hT : 0 < T) (hT' : 0 < T')
    (F : (Fin (r + 1) → ℂ) → ℝ≥0∞) :
    ∫⁻ q : (Fin r → ℂ) × ℂ, ENNReal.ofReal (Formalism.QuantumDeterminants.bcWeight k r T T' q) * F (coordSc r 1 q) =
      ENNReal.ofReal ((2 ^ (r + 1))⁻¹) *
        ∫⁻ c in GoodLoc (r := r) T T', ENNReal.ofReal (wtLoc k T T' c) * F c ∂(dcLoc (r := r)) := by
  rw [coordW_exact r k T T' 1 hk hT hT' one_pos F, nrm_one, lamW_one, mul_one, mul_one]

end Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL
