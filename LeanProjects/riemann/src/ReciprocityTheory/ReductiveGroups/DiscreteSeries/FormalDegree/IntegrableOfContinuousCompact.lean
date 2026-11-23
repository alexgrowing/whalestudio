import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.SumInnerBasisSqEqAdjoint
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.AdKMeasurePreserving
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.EigenvectorUnitaryMulStar
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.PBridge
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.PolarBasic
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.DetPPos
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.KinstSecondCountable

noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

theorem leading_minor_exp_re_pos {ε : Fin n → Bool} (y : PCoord ε → ℂ) {i : ℕ} (hi : i ≤ n) :
    0 < (Del (NormedSpace.exp (pmat y)) i).re := by
  have h := lemma3a y hi 1
  simp only [Complex.ofReal_one, one_smul, one_mul] at h
  rw [h, Complex.re_sum]
  have hw := lemma3b y hi
  have hnn : ∀ S, 0 ≤ wS y hi S := fun S => by unfold wS; positivity
  obtain ⟨S, -, hS⟩ : ∃ S ∈ (univ : Finset _), 0 < wS y hi S := by
    by_contra hc
    push Not at hc
    have : ∑ S, wS y hi S ≤ 0 := Finset.sum_nonpos (fun S hS => hc S hS)
    linarith
  refine Finset.sum_pos' (fun S _ => ?_) ⟨S, Finset.mem_univ _, ?_⟩
  · rw [← Complex.ofReal_exp, ← Complex.ofReal_mul, Complex.ofReal_re]
    exact mul_nonneg (hnn S) (Real.exp_pos _).le
  · rw [← Complex.ofReal_exp, ← Complex.ofReal_mul, Complex.ofReal_re]
    exact mul_pos hS (Real.exp_pos _)

theorem continuous_leading_minor (i : ℕ) : Continuous (fun A : Matrix (Fin n) (Fin n) ℂ => Del A i) := by
  by_cases h : i ≤ n
  · simp only [Del, dif_pos h]
    first
    | exact (continuous_id.matrix_submatrix _ _).matrix_det
    | fun_prop
  · simp only [Del, dif_neg h]
    exact continuous_const

section
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
theorem continuous_matrix_exp :
    Continuous (NormedSpace.exp : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ) := by
  first
  | exact NormedSpace.exp_continuous
  | exact NormedSpace.exp_continuous ℂ
  | exact NormedSpace.exp_continuous (𝕂 := ℂ)
  | fun_prop
end

theorem continuousAt_potential {ε : Fin n → Bool} (lam : Fin n → ℝ) (y : PCoord ε → ℂ) :
    ContinuousAt (Ph lam) (pmat y) := by
  show ContinuousAt (fun X => ∑ i ∈ range (n - 1), sCoef lam i * Fi X (i + 1)) (pmat y)
  have key : ∀ i ∈ range (n - 1),
      ContinuousAt (fun X : Matrix (Fin n) (Fin n) ℂ => sCoef lam i * Fi X (i + 1)) (pmat y) := by
    intro i hi
    have hi' : i + 1 ≤ n := by
      have := Finset.mem_range.1 hi
      omega
    have hc : Continuous (fun X : Matrix (Fin n) (Fin n) ℂ => (Del (NormedSpace.exp X) (i + 1)).re) :=
      Complex.continuous_re.comp ((continuous_leading_minor (i + 1)).comp continuous_matrix_exp)
    exact continuousAt_const.mul (hc.continuousAt.log (leading_minor_exp_re_pos y hi').ne')
  exact tendsto_finset_sum _ key

theorem continuous_potential_comp {ε : Fin n → Bool} (lam : Fin n → ℝ) {α : Type*} [TopologicalSpace α]
    {M : α → Matrix (Fin n) (Fin n) ℂ} (hM : Continuous M) (hp : ∀ a, ∃ y : PCoord ε → ℂ, M a = pmat y) :
    Continuous (fun a => Ph lam (M a)) := by
  refine continuous_iff_continuousAt.2 fun a => ?_
  obtain ⟨y, hy⟩ := hp a
  have h1 : ContinuousAt (Ph lam) (M a) := by
    rw [hy]
    exact continuousAt_potential lam y
  exact ContinuousAt.comp (g := Ph lam) h1 hM.continuousAt

theorem continuous_toMK_formal_degree (ε : Fin n → Bool) : Continuous (fun k : KG ε => toMK k) := by
  first
  | fun_prop
  | exact continuous_subtype_val.comp continuous_subtype_val
  | (unfold toMK; fun_prop)
  | (unfold toMK; exact continuous_subtype_val.comp continuous_subtype_val)
  | (unfold toMK; exact continuous_subtype_val.comp (continuous_subtype_val.comp continuous_subtype_val))

theorem continuous_potential_conj {ε : Fin n → Bool} (lam : Fin n → ℝ) (z : PCoord ε → ℂ) :
    Continuous (fun k : KG ε => Ph lam (toMK k⁻¹ * pmat z * toMK k)) := by
  refine continuous_potential_comp lam ?_ (fun k => ⟨adK k⁻¹ z, conj_pmat_eq_adK k z⟩)
  exact (((continuous_toMK_formal_degree ε).comp continuous_inv).mul continuous_const).mul (continuous_toMK_formal_degree ε)

private theorem continuous_pmat {ε : Fin n → Bool} : Continuous (fun y : PCoord ε → ℂ => pmat y) := by
  refine continuous_pi fun a => continuous_pi fun b => ?_
  by_cases h1 : b < a ∧ ε a ≠ ε b
  · simp only [pmat, dif_pos h1]
    exact continuous_apply _
  · by_cases h2 : a < b ∧ ε b ≠ ε a
    · simp only [pmat, dif_neg h1, dif_pos h2]
      exact (continuous_apply _).star
    · simp only [pmat, dif_neg h1, dif_neg h2]
      exact continuous_const

theorem continuous_potential_conj_prod {ε : Fin n → Bool} (lam : Fin n → ℝ) :
    Continuous (fun p : (PCoord ε → ℂ) × KG ε => Ph lam (toMK p.2⁻¹ * pmat p.1 * toMK p.2)) := by
  refine continuous_potential_comp lam ?_ (fun p => ⟨adK p.2⁻¹ p.1, conj_pmat_eq_adK p.2 p.1⟩)
  exact (((continuous_toMK_formal_degree ε).comp continuous_snd.inv).mul (continuous_pmat.comp continuous_fst)).mul
    ((continuous_toMK_formal_degree ε).comp continuous_snd)

theorem continuous_potential_pmat {ε : Fin n → Bool} (lam : Fin n → ℝ) :
    Continuous (fun y : PCoord ε → ℂ => Ph lam (pmat y)) := by
  have hpm : Continuous (fun y : PCoord ε → ℂ => pmat y) := by
    refine continuous_pi fun a => continuous_pi fun b => ?_
    by_cases h1 : b < a ∧ ε a ≠ ε b
    · simp only [pmat, dif_pos h1]
      exact continuous_apply _
    · by_cases h2 : a < b ∧ ε b ≠ ε a
      · simp only [pmat, dif_neg h1, dif_pos h2]
        exact (continuous_apply _).star
      · simp only [pmat, dif_neg h1, dif_neg h2]
        exact continuous_const
  exact continuous_potential_comp lam hpm (fun y => ⟨y, rfl⟩)

theorem continuous_exp_neg_potential_conj {ε : Fin n → Bool} (lam : Fin n → ℝ) (z : PCoord ε → ℂ) :
    Continuous (fun k : KG ε => Real.exp (-Ph lam (toMK k⁻¹ * pmat z * toMK k))) := by
  exact Real.continuous_exp.comp (continuous_potential_conj lam z).neg

theorem KType_op_inv_eq_adjoint {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) (k : KG ε) :
    T.op k⁻¹ = ContinuousLinearMap.adjoint (T.op k) := by
  rw [← ContinuousLinearMap.star_eq_adjoint]
  show ((T.τ k⁻¹ : unitary (T.V →L[ℂ] T.V)) : T.V →L[ℂ] T.V) = star ((T.τ k : unitary (T.V →L[ℂ] T.V)) : T.V →L[ℂ] T.V)
  rw [map_inv]
  rfl

theorem KType_norm_op_apply {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) (k : KG ε) (v : T.V) :
    ‖T.op k v‖ = ‖v‖ := by
  first
  | exact ContinuousLinearMap.norm_map_of_mem_unitary (T.τ k).2 v
  | exact unitary.norm_map (T.τ k) v
  | (have hu : ContinuousLinearMap.adjoint (T.op k) * T.op k = 1 := by
        rw [← ContinuousLinearMap.star_eq_adjoint]
        exact unitary.star_mul_self_of_mem (T.τ k).2
     have h : ((‖T.op k v‖ : ℂ)) ^ 2 = ((‖v‖ : ℂ)) ^ 2 := by
        rw [← inner_self_eq_norm_sq_to_K, ← inner_self_eq_norm_sq_to_K,
          ← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.mul_apply, hu,
          ContinuousLinearMap.one_apply]
     have h' : ‖T.op k v‖ ^ 2 = ‖v‖ ^ 2 := by exact_mod_cast h
     nlinarith [norm_nonneg (T.op k v), norm_nonneg v])

theorem KType_continuous_op {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) :
    Continuous (fun k => T.op k) := by
  exact continuous_subtype_val.comp T.cont

theorem integrable_dk_of_continuous {ε : Fin n → Bool} {E : Type*} [NormedAddCommGroup E] {g : KG ε → E} (hg : Continuous g) :
    Integrable g (dk ε) := by
  first
  | exact hg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace g)
  | exact (BoundedContinuousFunction.mkOfCompact ⟨g, hg⟩).integrable (dk ε)

theorem fF_eq_integral {ε : Fin n → Bool} (lam : Fin n → ℝ) {Λ : Fin n → ℝ} (T : KType ε Λ)
    (X : Matrix (Fin n) (Fin n) ℂ) :
    fF ε lam T X = ((Module.finrank ℂ T.V : ℝ) : ℂ) • ∫ k, ((Real.exp (-Ph lam (toMK k⁻¹ * X * toMK k)) : ℝ) : ℂ) •
      (T.op k * projW T * T.op k⁻¹) ∂(dk ε) := by
  unfold fF dk
  rw [integral_smul_measure, ← Complex.coe_smul, smul_smul]
  congr 1
  rw [ENNReal.toReal_inv]
  push_cast
  ring

theorem conj_projection_apply {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) (k : KG ε) (v : T.V) :
    (T.op k * projW T * T.op k⁻¹) v = ⟪T.op k T.w, v⟫_ℂ • T.op k T.w := by
  rw [KType_op_inv_eq_adjoint]
  first
  | (simp only [ContinuousLinearMap.mul_apply, projW, ContinuousLinearMap.smulRight_apply,
      innerSL_apply, ContinuousLinearMap.adjoint_inner_right, map_smul]; done)
  | (simp [projW, ContinuousLinearMap.adjoint_inner_right]; done)

theorem inner_fF_eq_integral {ε : Fin n → Bool} (lam : Fin n → ℝ) {Λ : Fin n → ℝ} (T : KType ε Λ) (z : PCoord ε → ℂ)
    (u v : T.V) :
    ⟪u, fF ε lam T (pmat z) v⟫_ℂ = ((Module.finrank ℂ T.V : ℝ) : ℂ) *
      ∫ k, ((Real.exp (-Ph lam (toMK k⁻¹ * pmat z * toMK k)) : ℝ) : ℂ) *
        (⟪T.op k T.w, v⟫_ℂ * ⟪u, T.op k T.w⟫_ℂ) ∂(dk ε) := by
  have hFc : Continuous (fun k : KG ε => ((Real.exp (-Ph lam (toMK k⁻¹ * pmat z * toMK k)) : ℝ) : ℂ) •
      (T.op k * projW T * T.op k⁻¹)) :=
    (Complex.continuous_ofReal.comp (continuous_exp_neg_potential_conj lam z)).smul
      (((KType_continuous_op T).mul continuous_const).mul ((KType_continuous_op T).comp continuous_inv))
  have hv : Continuous (fun k : KG ε => (((Real.exp (-Ph lam (toMK k⁻¹ * pmat z * toMK k)) : ℝ) : ℂ) •
      (T.op k * projW T * T.op k⁻¹)) v) := hFc.clm_apply continuous_const
  rw [fF_eq_integral, ContinuousLinearMap.smul_apply, inner_smul_right,
    ContinuousLinearMap.integral_apply (integrable_dk_of_continuous hFc) v, ← integral_inner (integrable_dk_of_continuous hv) u]
  congr 1
  refine integral_congr_ae (ae_of_all _ fun k => ?_)
  simp only [ContinuousLinearMap.smul_apply, conj_projection_apply, inner_smul_right]

theorem norm_inner_fF_le_half_sq_add_integral {ε : Fin n → Bool} (lam : Fin n → ℝ) {Λ : Fin n → ℝ} (T : KType ε Λ) (z : PCoord ε → ℂ)
    (u v : T.V) :
    ‖⟪u, fF ε lam T (pmat z) v⟫_ℂ‖ ≤ (‖u‖ ^ 2 + (Module.finrank ℂ T.V : ℝ) *
      ∫ k, Real.exp (-Ph lam (toMK k⁻¹ * pmat z * toMK k)) ^ 2 * ‖⟪v, T.op k T.w⟫_ℂ‖ ^ 2 ∂(dk ε)) / 2 := by
  have := (dk_props ε).1
  have hD : (0:ℝ) ≤ Module.finrank ℂ T.V := Nat.cast_nonneg _
  have hfc := continuous_exp_neg_potential_conj lam z
  have hop := KType_continuous_op T
  have hcu : Continuous (fun k : KG ε => ‖⟪u, T.op k T.w⟫_ℂ‖ ^ 2) :=
    (continuous_const.inner (hop.clm_apply continuous_const)).norm.pow 2
  have hcv : Continuous (fun k : KG ε => ‖⟪v, T.op k T.w⟫_ℂ‖ ^ 2) :=
    (continuous_const.inner (hop.clm_apply continuous_const)).norm.pow 2
  have hGc : Continuous (fun k : KG ε => ((Real.exp (-Ph lam (toMK k⁻¹ * pmat z * toMK k)) : ℝ) : ℂ) *
      (⟪T.op k T.w, v⟫_ℂ * ⟪u, T.op k T.w⟫_ℂ)) :=
    (Complex.continuous_ofReal.comp hfc).mul (((hop.clm_apply continuous_const).inner continuous_const).mul
      (continuous_const.inner (hop.clm_apply continuous_const)))
  have hks := kschur_coef T u T.w
  rw [T.w_norm] at hks
  have hi1 : Integrable (fun k : KG ε => ‖⟪u, T.op k T.w⟫_ℂ‖ ^ 2 / 2) (dk ε) := integrable_dk_of_continuous (hcu.div_const 2)
  have hi2 : Integrable (fun k : KG ε => Real.exp (-Ph lam (toMK k⁻¹ * pmat z * toMK k)) ^ 2 *
      ‖⟪v, T.op k T.w⟫_ℂ‖ ^ 2 / 2) (dk ε) := integrable_dk_of_continuous (((hfc.pow 2).mul hcv).div_const 2)
  calc ‖⟪u, fF ε lam T (pmat z) v⟫_ℂ‖
      = (Module.finrank ℂ T.V : ℝ) * ‖∫ k, ((Real.exp (-Ph lam (toMK k⁻¹ * pmat z * toMK k)) : ℝ) : ℂ) *
        (⟪T.op k T.w, v⟫_ℂ * ⟪u, T.op k T.w⟫_ℂ) ∂(dk ε)‖ := by
        rw [inner_fF_eq_integral, norm_mul, Complex.norm_real, Real.norm_of_nonneg hD]
    _ ≤ (Module.finrank ℂ T.V : ℝ) * ∫ k, ‖((Real.exp (-Ph lam (toMK k⁻¹ * pmat z * toMK k)) : ℝ) : ℂ) *
        (⟪T.op k T.w, v⟫_ℂ * ⟪u, T.op k T.w⟫_ℂ)‖ ∂(dk ε) :=
        mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) hD
    _ ≤ (Module.finrank ℂ T.V : ℝ) * ∫ k, (‖⟪u, T.op k T.w⟫_ℂ‖ ^ 2 / 2 +
        Real.exp (-Ph lam (toMK k⁻¹ * pmat z * toMK k)) ^ 2 * ‖⟪v, T.op k T.w⟫_ℂ‖ ^ 2 / 2) ∂(dk ε) := by
        refine mul_le_mul_of_nonneg_left (integral_mono (integrable_dk_of_continuous (continuous_norm.comp hGc)) (hi1.add hi2)
          (fun k => ?_)) hD
        have he := (Real.exp_pos (-Ph lam (toMK k⁻¹ * pmat z * toMK k))).le
        simp only [norm_mul, Complex.norm_real, Real.norm_of_nonneg he]
        rw [norm_inner_symm (T.op k T.w) v]
        nlinarith [sq_nonneg (‖⟪u, T.op k T.w⟫_ℂ‖ - Real.exp (-Ph lam (toMK k⁻¹ * pmat z * toMK k)) *
          ‖⟪v, T.op k T.w⟫_ℂ‖)]
    _ = _ := by
        rw [integral_add hi1 hi2, integral_div, integral_div]
        linear_combination hks / 2

theorem lemma6b {ε : Fin n → Bool} {lam : Fin n → ℝ} (T : KType ε (lowK ε lam)) (z : PCoord ε → ℂ) :
    hsOp (fF ε lam T (pmat z)) ≤
      (Module.finrank ℂ T.V : ℝ) * ∫ k, Real.exp (-2 * Ph lam (toMK k⁻¹ * pmat z * toMK k)) ∂(dk ε) := by
  have hfc := continuous_exp_neg_potential_conj lam z
  have hop := KType_continuous_op T
  have hv : ∀ v : T.V, ‖fF ε lam T (pmat z) v‖ ^ 2 ≤ (Module.finrank ℂ T.V : ℝ) *
      ∫ k, Real.exp (-Ph lam (toMK k⁻¹ * pmat z * toMK k)) ^ 2 * ‖⟪v, T.op k T.w⟫_ℂ‖ ^ 2 ∂(dk ε) := by
    intro v
    have h := norm_inner_fF_le_half_sq_add_integral lam T z (fF ε lam T (pmat z) v) v
    have h1 : ‖⟪fF ε lam T (pmat z) v, fF ε lam T (pmat z) v⟫_ℂ‖ = ‖fF ε lam T (pmat z) v‖ ^ 2 := by
      rw [inner_self_eq_norm_sq_to_K]
      simp
    rw [h1] at h
    linarith
  have hterm : ∀ i, Continuous (fun k : KG ε => Real.exp (-Ph lam (toMK k⁻¹ * pmat z * toMK k)) ^ 2 *
      ‖⟪stdOrthonormalBasis ℂ T.V i, T.op k T.w⟫_ℂ‖ ^ 2) := fun i =>
    (hfc.pow 2).mul ((continuous_const.inner (hop.clm_apply continuous_const)).norm.pow 2)
  have hsq : ∀ x : ℝ, Real.exp (-x) ^ 2 = Real.exp (-2 * x) := fun x => by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  unfold hsOp
  calc ∑ i, ‖fF ε lam T (pmat z) (stdOrthonormalBasis ℂ T.V i)‖ ^ 2
      ≤ ∑ i, (Module.finrank ℂ T.V : ℝ) * ∫ k, Real.exp (-Ph lam (toMK k⁻¹ * pmat z * toMK k)) ^ 2 *
          ‖⟪stdOrthonormalBasis ℂ T.V i, T.op k T.w⟫_ℂ‖ ^ 2 ∂(dk ε) :=
        Finset.sum_le_sum (fun i _ => hv _)
    _ = (Module.finrank ℂ T.V : ℝ) * ∫ k, ∑ i, Real.exp (-Ph lam (toMK k⁻¹ * pmat z * toMK k)) ^ 2 *
          ‖⟪stdOrthonormalBasis ℂ T.V i, T.op k T.w⟫_ℂ‖ ^ 2 ∂(dk ε) := by
        rw [integral_finset_sum univ (fun i _ => integrable_dk_of_continuous (hterm i)), Finset.mul_sum]
    _ = _ := by
        congr 1
        refine integral_congr_ae (Filter.Eventually.of_forall (fun k => ?_))
        simp only
        rw [← Finset.mul_sum, OrthonormalBasis.sum_sq_norm_inner_right, KType_norm_op_apply, T.w_norm, one_pow,
          mul_one, hsq]

theorem jacobian_nonneg {ε : Fin n → Bool} (z : PCoord ε → ℂ) : 0 ≤ Jac z := by
  unfold Jac
  refine Finset.prod_nonneg fun a _ => Finset.prod_nonneg fun b _ => ?_
  unfold shc
  split_ifs with hu
  · norm_num
  · rcases lt_or_gt_of_ne hu with h | h
    · exact div_nonneg_of_nonpos (Real.sinh_neg_iff.2 h).le h.le
    · exact div_nonneg (Real.sinh_pos_iff.2 h).le h.le

theorem lintegral_conj_invariant {ε : Fin n → Bool} (lam : Fin n → ℝ) (k : KG ε) :
    ∫⁻ z : PCoord ε → ℂ, ENNReal.ofReal (Real.exp (-2 * Ph lam (toMK k⁻¹ * pmat z * toMK k))) *
      ENNReal.ofReal (Jac z) =
      ∫⁻ z : PCoord ε → ℂ, ENNReal.ofReal (Real.exp (-2 * Ph lam (pmat z)) * Jac z) := by
  have hG : Measurable (fun y : PCoord ε → ℂ => ENNReal.ofReal (Real.exp (-2 * Ph lam (pmat y)) * Jac y)) :=
    ENNReal.measurable_ofReal.comp
      ((Real.continuous_exp.comp (continuous_const.mul (continuous_potential_pmat lam))).mul
        (jac_continuous ε)).measurable
  rw [← (adK_measurePreserving k⁻¹).lintegral_comp hG]
  refine lintegral_congr (fun z => ?_)
  simp only [conj_pmat_eq_adK, jac_adK]
  rw [ENNReal.ofReal_mul (Real.exp_pos _).le]

theorem lemma6c {ε : Fin n → Bool} {lam : Fin n → ℝ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {T : KType ε (lowK ε lam)}
    {j : T.V →L[ℂ] H} (hF : FData ε lam σ T j) {d : ℝ} (hd : Formalism.MainNotions.S.IsFdeg (muCD ε) σ d) :
    ENNReal.ofReal (1 / d) ≤ ENNReal.ofReal (cPQ ε / Module.finrank ℂ T.V) *
      ∫⁻ z : PCoord ε → ℂ, ENNReal.ofReal (Real.exp (-2 * Ph lam (pmat z)) * Jac z) := by
  rcases le_or_gt d 0 with hd0 | hd0
  · rw [ENNReal.ofReal_of_nonpos (by rw [one_div]; exact inv_nonpos.mpr hd0)]
    exact zero_le
  have := (dk_props ε).1
  have hD : (0:ℝ) < Module.finrank ℂ T.V := by
    have : Nontrivial T.V := ⟨⟨T.w, 0, fun h => by
      have h2 := T.w_norm
      rw [h, norm_zero] at h2
      exact zero_ne_one h2⟩⟩
    exact_mod_cast Module.finrank_pos
  have hD' : (Module.finrank ℂ T.V : ℝ) ≠ 0 := hD.ne'
  have hd' : d ≠ 0 := hd0.ne'
  have hc : 0 ≤ cPQ ε := by unfold cPQ; positivity
  have ha := lemma6a hF hd
  have hmeas : AEMeasurable (Function.uncurry fun (z : PCoord ε → ℂ) (k : KG ε) =>
      ENNReal.ofReal (Real.exp (-2 * Ph lam (toMK k⁻¹ * pmat z * toMK k))) * ENNReal.ofReal (Jac z))
      ((volume : Measure (PCoord ε → ℂ)).prod (dk ε)) := by
    refine Measurable.aemeasurable ?_
    exact (ENNReal.measurable_ofReal.comp (Real.continuous_exp.comp
      (continuous_const.mul (continuous_potential_conj_prod lam))).measurable).mul
      (ENNReal.measurable_ofReal.comp ((jac_continuous ε).comp continuous_fst).measurable)
  have hIa : ∫⁻ z : PCoord ε → ℂ, ENNReal.ofReal (hsOp (fF ε lam T (pmat z)) * Jac z) ≤
      ENNReal.ofReal (Module.finrank ℂ T.V : ℝ) *
        ∫⁻ z : PCoord ε → ℂ, ENNReal.ofReal (Real.exp (-2 * Ph lam (pmat z)) * Jac z) := by
    calc ∫⁻ z : PCoord ε → ℂ, ENNReal.ofReal (hsOp (fF ε lam T (pmat z)) * Jac z)
        ≤ ∫⁻ z : PCoord ε → ℂ, ENNReal.ofReal (Module.finrank ℂ T.V : ℝ) *
            ∫⁻ k, ENNReal.ofReal (Real.exp (-2 * Ph lam (toMK k⁻¹ * pmat z * toMK k))) *
              ENNReal.ofReal (Jac z) ∂(dk ε) := by
          refine lintegral_mono (fun z => ?_)
          have hint : Integrable (fun k : KG ε => Real.exp (-2 * Ph lam (toMK k⁻¹ * pmat z * toMK k))) (dk ε) :=
            integrable_dk_of_continuous (Real.continuous_exp.comp (continuous_const.mul (continuous_potential_conj lam z)))
          have hnn : 0 ≤ ∫ k, Real.exp (-2 * Ph lam (toMK k⁻¹ * pmat z * toMK k)) ∂(dk ε) :=
            integral_nonneg (fun k => (Real.exp_pos _).le)
          calc ENNReal.ofReal (hsOp (fF ε lam T (pmat z)) * Jac z)
              ≤ ENNReal.ofReal ((Module.finrank ℂ T.V : ℝ) *
                  (∫ k, Real.exp (-2 * Ph lam (toMK k⁻¹ * pmat z * toMK k)) ∂(dk ε)) * Jac z) :=
                ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (lemma6b T z) (jacobian_nonneg z))
            _ = ENNReal.ofReal (Module.finrank ℂ T.V : ℝ) *
                  ((∫⁻ k, ENNReal.ofReal (Real.exp (-2 * Ph lam (toMK k⁻¹ * pmat z * toMK k))) ∂(dk ε)) *
                    ENNReal.ofReal (Jac z)) := by
                rw [ENNReal.ofReal_mul (mul_nonneg hD.le hnn), ENNReal.ofReal_mul hD.le,
                  ofReal_integral_eq_lintegral_ofReal hint
                    (Filter.Eventually.of_forall (fun k => (Real.exp_pos _).le)), mul_assoc]
            _ = _ := by rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
      _ = ENNReal.ofReal (Module.finrank ℂ T.V : ℝ) * ∫⁻ k, (∫⁻ z : PCoord ε → ℂ,
            ENNReal.ofReal (Real.exp (-2 * Ph lam (toMK k⁻¹ * pmat z * toMK k))) *
              ENNReal.ofReal (Jac z)) ∂(dk ε) := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_lintegral_swap hmeas]
      _ = _ := by
          simp only [lintegral_conj_invariant]
          rw [lintegral_const, measure_univ, mul_one]
  calc ENNReal.ofReal (1 / d)
      = ENNReal.ofReal (1 / (Module.finrank ℂ T.V : ℝ) ^ 2) *
          ENNReal.ofReal ((Module.finrank ℂ T.V : ℝ) ^ 2 / d) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        field_simp
    _ = ENNReal.ofReal (1 / (Module.finrank ℂ T.V : ℝ) ^ 2) * (ENNReal.ofReal (cPQ ε) *
          ∫⁻ z : PCoord ε → ℂ, ENNReal.ofReal (hsOp (fF ε lam T (pmat z)) * Jac z)) := by rw [ha]
    _ ≤ ENNReal.ofReal (1 / (Module.finrank ℂ T.V : ℝ) ^ 2) * (ENNReal.ofReal (cPQ ε) *
          (ENNReal.ofReal (Module.finrank ℂ T.V : ℝ) *
            ∫⁻ z : PCoord ε → ℂ, ENNReal.ofReal (Real.exp (-2 * Ph lam (pmat z)) * Jac z))) :=
        by gcongr
    _ = _ := by
        rw [← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (mul_nonneg (by positivity) hc)]
        congr 2
        field_simp

end ReciprocityTheory.ChartRestriction.DS
