import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.SumBoundStatementPfA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OrthoStatementPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LUStatementPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ExtFStatementPfB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.OrthonormalFlagTranslateHolds

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix ComplexOrder

namespace GlobalTheory.FramePotential

theorem one_le_norm_lminor_sq {n p : ℕ} (h : p ≤ n) (g : Matrix (Fin n) (Fin n) ℂ)
    (hg : gᵀ * (Matrix.diagonal fun a : Fin n => ((sgn p (a : ℕ) : ℝ) : ℂ)) * g.map (starRingEnd ℂ) =
      Matrix.diagonal fun a : Fin n => ((sgn p (a : ℕ) : ℝ) : ℂ)) :
    1 ≤ ‖lminor g ⟨p, Nat.lt_succ_of_le h⟩‖ ^ 2 := by
  set A : Matrix (Fin p) (Fin p) ℂ := g.submatrix (Fin.castLE h) (Fin.castLE h) with hA
  set C : Matrix (Fin n) (Fin p) ℂ :=
    Matrix.of fun k a => if (k : ℕ) < p then 0 else g k (Fin.castLE h a) with hC
  have key : Aᴴ * A = 1 + Cᴴ * C := by
    ext a b
    have e := congrFun (congrFun hg (Fin.castLE h b)) (Fin.castLE h a)
    rw [Matrix.mul_apply] at e
    simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Matrix.map_apply,
      Matrix.diagonal_apply, Fin.castLE_inj] at e
    have e1 : (1 : Matrix (Fin p) (Fin p) ℂ) a b =
        ∑ k, g k (Fin.castLE h b) * ((sgn p (k : ℕ) : ℝ) : ℂ) * starRingEnd ℂ (g k (Fin.castLE h a)) := by
      rw [e, Matrix.one_apply]
      by_cases hab : a = b
      · subst hab; simp [sgn]
      · rw [if_neg hab, if_neg (Ne.symm hab)]
    have e2 : (Aᴴ * A) a b = ∑ k : Fin n, if (k : ℕ) < p then
        starRingEnd ℂ (g k (Fin.castLE h a)) * g k (Fin.castLE h b) else 0 := by
      rw [Matrix.mul_apply]
      refine Fintype.sum_of_injective (Fin.castLE h) (Fin.castLE_injective h) _ _ (fun k hk => ?_)
        (fun k => ?_)
      · rw [if_neg]
        intro hlt
        exact hk ⟨⟨k, hlt⟩, Fin.ext rfl⟩
      · simp [hA, Matrix.conjTranspose_apply]
    rw [e2, Matrix.add_apply, e1, Matrix.mul_apply, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hk : (k : ℕ) < p
    · simp [hC, sgn, hk, Matrix.conjTranspose_apply, mul_comm]
    · simp [hC, sgn, hk, Matrix.conjTranspose_apply, mul_comm]
  have h1 := sumBd_det_one_add_ge (Matrix.posSemidef_conjTranspose_mul_self C)
  rw [← key, sumBd_normSq_det, sumBd_trace_ctm] at h1
  have h2 := sumBdFsq_nonneg C
  rw [← Complex.normSq_eq_norm_sq]
  show 1 ≤ Complex.normSq A.det
  linarith

theorem lminor_mul_upper {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) {B : Matrix (Fin n) (Fin n) ℂ}
    (hB : B.BlockTriangular id) (k : Fin (n + 1)) :
    lminor (M * B) k = lminor M k * ∏ j : Fin k, B (Fin.castLE (Nat.le_of_lt_succ k.isLt) j)
      (Fin.castLE (Nat.le_of_lt_succ k.isLt) j) := by
  have h := Nat.le_of_lt_succ k.isLt
  unfold lminor
  rw [FrameDegreeData.sub_mul_sub h M B (fun a c m hm => by
      rw [FrameDegreeData.upper_lt hB (show Fin.castLE h c < m by rw [Fin.lt_def]; simp; omega), mul_zero]),
    Matrix.det_mul, FrameDegreeData.det_sub_upper h hB]

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem factor_rmul {r : ℕ} (X : Data E r) (x0 x : Frame X.Ψ r) {b : Frame X.Ψ r}
    (hb : b ∈ Bor X.Ψ r) (τ : X.Ψ) (i : Fin (r + 1)) :
    ‖dmin X.Gm (rmul x b) τ i‖ / ‖lminor ((mat x0 τ)⁻¹ * mat (rmul x b) τ) i‖ ^ 2 =
      ‖dmin X.Gm x τ i‖ / ‖lminor ((mat x0 τ)⁻¹ * mat x τ) i‖ ^ 2 := by
  have e : mat (rmul x b) τ = mat x τ * mat b τ := rfl
  rw [FrameDegreeData.dmin_rmul X x hb, e, ← Matrix.mul_assoc,
    lminor_mul_upper _ (FrameDegreeData.upper_of_bor X hb τ)]
  have hc : (∏ j : Fin i, mat b τ (Fin.castLE (Nat.le_of_lt_succ i.isLt) j)
      (Fin.castLE (Nat.le_of_lt_succ i.isLt) j)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun j _ => FrameDegreeData.bdiag_ne X hb τ _
  generalize (∏ j : Fin i, mat b τ (Fin.castLE (Nat.le_of_lt_succ i.isLt) j)
      (Fin.castLE (Nat.le_of_lt_succ i.isLt) j)) = c at hc ⊢
  have hc' : ‖c‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hc)
  rw [norm_mul, norm_mul, norm_mul, Complex.norm_conj, mul_pow,
    ← mul_div_mul_right ‖dmin X.Gm x τ i‖ _ hc']
  congr 1
  ring

theorem norm_dmin_of_isOrth {r : ℕ} (X : Data E r) {x : Frame X.Ψ r} (hx : IsOrth X x) (τ : X.Ψ)
    (i : Fin (r + 1)) : ‖dmin X.Gm x τ i‖ = 1 := by
  unfold dmin lminor
  rw [hx τ, Matrix.submatrix_diagonal _ _ (Fin.castLE_injective _),
    Matrix.det_diagonal, norm_prod]
  refine Finset.prod_eq_one fun a _ => ?_
  simp only [Function.comp, sgn]
  split_ifs <;> simp

theorem one_le_minor_of_isOrth {r : ℕ} (X : Data E r) {x0 x : Frame X.Ψ r} (h0 : IsOrth X x0)
    (hx : IsOrth X x) (τ : X.Ψ) :
    1 ≤ ‖lminor ((mat x0 τ)⁻¹ * mat x τ) ⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩‖ ^ 2 := by
  apply one_le_norm_lminor_sq X.p0_le
  have hu : IsUnit (mat x0 τ).det := isUnit_iff_ne_zero.mpr (LUPf.orthogonalFrame_det_ne_zero X x0 h0 τ)
  conv_lhs => rw [← h0 τ]
  rw [← FrameDegreeData.gram_mul, Matrix.mul_nonsing_inv_cancel_left _ _ hu, hx τ]

theorem factor_mem {r : ℕ} (X : Data E r) {x0 x : Frame X.Ψ r} (h0 : IsOrth X x0)
    (hx : x ∈ X.dom) (τ : X.Ψ) :
    0 < ‖dmin X.Gm x τ ⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩‖ /
        ‖lminor ((mat x0 τ)⁻¹ * mat x τ) ⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩‖ ^ 2 ∧
      ‖dmin X.Gm x τ ⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩‖ /
        ‖lminor ((mat x0 τ)⁻¹ * mat x τ) ⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩‖ ^ 2 ≤ 1 := by
  obtain ⟨x1, h1, b, hb, rfl⟩ := ortho_holds r X x hx
  rw [factor_rmul X x0 x1 hb, norm_dmin_of_isOrth X h1]
  have h := one_le_minor_of_isOrth X h0 h1 τ
  exact ⟨div_pos one_pos (by linarith), (div_le_one (by linarith)).mpr h⟩

theorem lminor_cpt {r : ℕ} (X : Data E r) {x0 : Frame X.Ψ r} (h0 : IsOrth X x0) (z : V (nd X))
    (τ : X.Ψ) (i : Fin (r + 1)) : lminor ((mat x0 τ)⁻¹ * mat (cpt X x0 z) τ) i = 1 := by
  have hu : IsUnit (mat x0 τ).det := isUnit_iff_ne_zero.mpr (LUPf.orthogonalFrame_det_ne_zero X x0 h0 τ)
  have e : mat (cpt X x0 z) τ = mat x0 τ * mat (nmat X z) τ := rfl
  rw [e, Matrix.nonsing_inv_mul_cancel_left _ _ hu, ← Matrix.mul_one (mat (nmat X z) τ),
    LUPf.lminor_nb _ _ (fun a c hac => ?_) (fun a => ?_) Matrix.blockTriangular_one]
  · simp
  · simp [mat, nmat, hac.ne, not_lt.mpr hac.le]
  · simp [mat, nmat]

theorem frame_potential_basic :
    (∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 → Measurable (fun x : Frame X.Ψ r => (∏ τ : X.Ψ, ‖dmin X.Gm (x) τ (⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩ : Fin (r + 1))‖ / ‖lminor ((mat x0 τ)⁻¹ * mat (x) τ) (⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩ : Fin (r + 1))‖ ^ 2)) ∧ (∀ x ∈ X.dom, 0 < (∏ τ : X.Ψ, ‖dmin X.Gm (x) τ (⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩ : Fin (r + 1))‖ / ‖lminor ((mat x0 τ)⁻¹ * mat (x) τ) (⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩ : Fin (r + 1))‖ ^ 2) ∧ (∏ τ : X.Ψ, ‖dmin X.Gm (x) τ (⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩ : Fin (r + 1))‖ / ‖lminor ((mat x0 τ)⁻¹ * mat (x) τ) (⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩ : Fin (r + 1))‖ ^ 2) ≤ 1) ∧ (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, (∏ τ : X.Ψ, ‖dmin X.Gm (rmul x b) τ (⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩ : Fin (r + 1))‖ / ‖lminor ((mat x0 τ)⁻¹ * mat (rmul x b) τ) (⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩ : Fin (r + 1))‖ ^ 2) = (∏ τ : X.Ψ, ‖dmin X.Gm (x) τ (⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩ : Fin (r + 1))‖ / ‖lminor ((mat x0 τ)⁻¹ * mat (x) τ) (⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩ : Fin (r + 1))‖ ^ 2)) ∧ ∀ z ∈ OmF X x0, (∏ τ : X.Ψ, ‖dmin X.Gm (cpt X x0 z) τ (⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩ : Fin (r + 1))‖ / ‖lminor ((mat x0 τ)⁻¹ * mat (cpt X x0 z) τ) (⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩ : Fin (r + 1))‖ ^ 2) = Real.exp (-rhF X x0 z)) := by
  intro r X x0 h0
  refine ⟨?_, fun x hx => ⟨?_, ?_⟩, fun x _ b hb => ?_, fun z hz => ?_⟩
  · refine Finset.measurable_prod _ fun τ _ => Measurable.div ?_ ?_
    · exact (ExtFPf.cont_dmin X τ _).norm.measurable
    · have hm : Continuous fun x : Frame X.Ψ r => mat x τ := continuous_apply τ
      exact ((((continuous_const.matrix_mul hm).matrix_submatrix _ _).matrix_det).norm.pow 2).measurable
  · exact Finset.prod_pos fun τ _ => (factor_mem X h0 hx τ).1
  · exact Finset.prod_le_one (fun τ _ => (factor_mem X h0 hx τ).1.le)
      fun τ _ => (factor_mem X h0 hx τ).2
  · exact Finset.prod_congr rfl fun τ _ => factor_rmul X x0 x hb τ _
  · unfold rhF
    rw [neg_neg, Real.exp_sum]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [lminor_cpt X h0, Real.exp_log (norm_pos_iff.mpr (FlowCoefficientBounds.dmin_ne X hz τ _))]
    simp

end GlobalTheory.FramePotential
