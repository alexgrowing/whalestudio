import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.SumBoundStatementPfC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfS
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpCStatementPfA

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.FrameSumBound

def swapIdx {r p : ℕ} (hp : p ≤ r) : Fin (r - p) ⊕ Fin p ≃ Fin r :=
  ((Equiv.sumComm _ _).trans finSumFinEquiv).trans (finCongr (by omega))

theorem swapIdx_inr {r p : ℕ} (hp : p ≤ r) (a : Fin p) :
    swapIdx hp (Sum.inr a) = Fin.castLE hp a := by
  ext; simp [swapIdx]

theorem swapIdx_inl_val {r p : ℕ} (hp : p ≤ r) (a : Fin (r - p)) :
    ((swapIdx hp (Sum.inl a) : Fin r) : ℕ) = p + a := by
  simp [swapIdx]

theorem sgn_submatrix {r p : ℕ} (hp : p ≤ r) :
    (Matrix.diagonal fun a : Fin r => ((sgn p (a : ℕ) : ℝ) : ℂ)).submatrix (swapIdx hp) (swapIdx hp) =
      -Jf (r - p) p := by
  rw [Matrix.submatrix_diagonal_equiv]
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · by_cases h : i = j
    · subst h; simp [Jf, swapIdx_inl_val, sgn]
    · simp [Jf, h, Matrix.one_apply_ne h]
  · simp [Jf]
  · simp [Jf]
  · by_cases h : i = j
    · subst h; simp [Jf, swapIdx_inr, sgn]
    · simp [Jf, h, Matrix.one_apply_ne h]

theorem isUpq_submatrix {r p : ℕ} (hp : p ≤ r) {g : Matrix (Fin r) (Fin r) ℂ}
    (hg : gᵀ * (Matrix.diagonal fun a : Fin r => ((sgn p (a : ℕ) : ℝ) : ℂ)) * g.map (starRingEnd ℂ) =
      Matrix.diagonal fun a : Fin r => ((sgn p (a : ℕ) : ℝ) : ℂ)) :
    IsUpq (g.submatrix (swapIdx hp) (swapIdx hp)) := by
  set J : Matrix (Fin r) (Fin r) ℂ := Matrix.diagonal fun a : Fin r => ((sgn p (a : ℕ) : ℝ) : ℂ) with hJ
  have hJT : Jᵀ = J := Matrix.diagonal_transpose _
  have h1 : gᴴ * J * g = J := by
    have := congrArg Matrix.transpose hg
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hJT,
      ← Matrix.mul_assoc] at this
    exact this
  have h2 : Jf (r - p) p = -(J.submatrix (swapIdx hp) (swapIdx hp)) := by
    rw [hJ, sgn_submatrix, neg_neg]
  unfold IsUpq
  rw [h2, Matrix.conjTranspose_submatrix, Matrix.mul_neg, Matrix.neg_mul,
    Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, h1]

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem isOrth_lact {r : ℕ} (X : Data E r) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) {x : Frame X.Ψ r}
    (hx : IsOrth X x) : IsOrth X (lact γ x) := fun τ => by
  rw [OntoS.gram_lact X hγ, hx τ]

theorem isUpq_frame {r : ℕ} (X : Data E r) {x0 y : Frame X.Ψ r} (h0 : IsOrth X x0)
    (hy : IsOrth X y) (τ : X.Ψ) :
    IsUpq (((mat x0 τ)⁻¹ * mat y τ).submatrix (swapIdx X.p0_le) (swapIdx X.p0_le)) := by
  apply isUpq_submatrix
  have hu : IsUnit (mat x0 τ).det := isUnit_iff_ne_zero.mpr (ExF.det_ne_of_orth X h0 τ)
  have h := hy τ
  conv_lhs at h => rw [← Matrix.mul_nonsing_inv_cancel_left (mat x0 τ) (mat y τ) hu]
  rw [FrameDegreeData.gram_mul, h0 τ] at h
  exact h

theorem quot_eq {r : ℕ} (X : Data E r) {x0 x : Frame X.Ψ r} (h0 : IsOrth X x0) (hx : IsOrth X x)
    (γ δ : GL (Fin r) E) (τ : X.Ψ) :
    ((mat x0 τ)⁻¹ * mat (lact δ x) τ) * ((mat x0 τ)⁻¹ * mat (lact γ x) τ)⁻¹ =
      (mat x0 τ)⁻¹ * ((δ * γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 * mat x0 τ := by
  have hu0 : IsUnit (mat x0 τ).det := isUnit_iff_ne_zero.mpr (ExF.det_ne_of_orth X h0 τ)
  have hu : IsUnit (mat x τ).det := isUnit_iff_ne_zero.mpr (ExF.det_ne_of_orth X hx τ)
  have e1 : ∀ γ : GL (Fin r) E,
      mat (lact γ x) τ = (γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ := fun _ => rfl
  have hγ : ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 *
      (γ : Matrix (Fin r) (Fin r) E).map τ.1 = 1 := by
    rw [← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero τ.1) (map_one τ.1)]
  have hinv : ((mat x0 τ)⁻¹ * mat (lact γ x) τ)⁻¹ =
      (mat x τ)⁻¹ * (((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 * mat x0 τ) := by
    apply Matrix.inv_eq_left_inv
    rw [e1]
    simp only [Matrix.mul_assoc]
    rw [Matrix.mul_nonsing_inv_cancel_left _ _ hu0, ← Matrix.mul_assoc _ _ (mat x τ), hγ,
      Matrix.one_mul, Matrix.nonsing_inv_mul _ hu]
  rw [hinv, e1, Units.val_mul, Matrix.map_mul]
  simp only [Matrix.mul_assoc]
  rw [Matrix.mul_nonsing_inv_cancel_left _ _ hu]

theorem frame_sum_bound :
    (∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 → PropDisc X → ∃ c : ℝ, 0 < c ∧ ∀ γ ∈ X.Γ, γ ≠ 1 → ∃ (τ : X.Ψ) (a b : Fin r), c ≤ ‖((mat x0 τ)⁻¹ * (γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x0 τ - 1) a b‖) → (∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 → PropDisc X → ∀ s : ℝ, 2 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 < s → ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ x, IsOrth X x → ∑' γ : X.Γ, ENNReal.ofReal ((∏ τ : X.Ψ, ‖dmin X.Gm (lact γ.1 x) τ (⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩ : Fin (r + 1))‖ / ‖lminor ((mat x0 τ)⁻¹ * mat (lact γ.1 x) τ) (⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩ : Fin (r + 1))‖ ^ 2) ^ s) ≤ C) := by
  intro hsep r X x0 h0 hPD s hs
  obtain ⟨c, hc, hcs⟩ := hsep r X x0 h0 hPD
  have hr : r - X.p0 + X.p0 = r := Nat.sub_add_cancel X.p0_le
  obtain ⟨C, hC, hb⟩ := sumBd_sum (p := r - X.p0) (q := X.p0) (f := X.Ψ.card) (s := s)
    (by rw [hr]; exact hs) hc
  refine ⟨C, hC, fun x hx => ?_⟩
  let eΨ : Fin X.Ψ.card ≃ X.Ψ := X.Ψ.equivFin.symm
  have key := hb X.Γ (fun γ k => ((mat x0 (eΨ k))⁻¹ * mat (lact γ.1 x) (eΨ k)).submatrix
      (swapIdx X.p0_le) (swapIdx X.p0_le))
    (fun γ k => isUpq_frame X h0 (isOrth_lact X γ.2 hx) _)
    (fun γ δ hne => by
      have hmem : δ.1 * γ.1⁻¹ ∈ X.Γ := X.Γ.mul_mem δ.2 (X.Γ.inv_mem γ.2)
      have hne1 : δ.1 * γ.1⁻¹ ≠ 1 := fun h => hne (Subtype.ext (mul_inv_eq_one.mp h).symm)
      obtain ⟨τ, a, b, hab⟩ := hcs _ hmem hne1
      refine ⟨eΨ.symm τ, (swapIdx X.p0_le).symm a, (swapIdx X.p0_le).symm b, ?_⟩
      rw [Equiv.apply_symm_apply, Matrix.inv_submatrix_equiv, Matrix.submatrix_mul_equiv,
        quot_eq X h0 hx, Matrix.submatrix_apply, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
      rw [Matrix.sub_apply] at hab
      convert hab using 3
      simp [Matrix.one_apply])
  refine le_trans (le_of_eq ?_) key
  refine tsum_congr fun γ => ?_
  congr 1
  rw [← Real.finset_prod_rpow _ _ (fun τ _ => by positivity), ← eΨ.prod_comp]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [IC.norm_dmin_orth X (isOrth_lact X γ.2 hx), one_div, Complex.normSq_eq_norm_sq]
  have hm : ∀ M : Matrix (Fin r) (Fin r) ℂ,
      lminor M (⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩ : Fin (r + 1)) =
        (M.submatrix (swapIdx X.p0_le) (swapIdx X.p0_le)).toBlocks₂₂.det := fun M => by
    unfold lminor
    congr 1
  rw [hm]

end GlobalTheory.FrameSumBound
