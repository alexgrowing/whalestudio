import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetMeasStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ExhaustFStatementPfC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ExtFStatementPfA

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.KU

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Matrix
open scoped ENNReal ComplexOrder

noncomputable section

section

def Yb {p q : ℕ} (M : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) : Matrix (Fin p) (Fin q) ℂ :=
  M.toBlocks₁₂ * M.toBlocks₂₂⁻¹

theorem toBlocks₁₂_mul {p q : ℕ} (g M : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) :
    (g * M).toBlocks₁₂ = g.toBlocks₁₁ * M.toBlocks₁₂ + g.toBlocks₁₂ * M.toBlocks₂₂ := by
  ext i j; simp [toBlocks₁₂, toBlocks₁₁, toBlocks₂₂, Matrix.mul_apply, Fintype.sum_sum_type]

theorem toBlocks₂₂_mul {p q : ℕ} (g M : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) :
    (g * M).toBlocks₂₂ = g.toBlocks₂₁ * M.toBlocks₁₂ + g.toBlocks₂₂ * M.toBlocks₂₂ := by
  ext i j; simp [toBlocks₁₂, toBlocks₂₁, toBlocks₂₂, Matrix.mul_apply, Fintype.sum_sum_type]

theorem Yb_mul {p q : ℕ} (g M : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) (hM : M.toBlocks₂₂.det ≠ 0) :
    Yb (g * M) = mob g (Yb M) := by
  have hu : IsUnit M.toBlocks₂₂.det := isUnit_iff_ne_zero.mpr hM
  have h12 : M.toBlocks₁₂ = Yb M * M.toBlocks₂₂ := by
    rw [Yb, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.mul_one]
  have e1 : (g * M).toBlocks₁₂ = (g.toBlocks₁₁ * Yb M + g.toBlocks₁₂) * M.toBlocks₂₂ := by
    rw [toBlocks₁₂_mul, h12, Matrix.add_mul, Matrix.mul_assoc]
  have e2 : (g * M).toBlocks₂₂ = (g.toBlocks₂₁ * Yb M + g.toBlocks₂₂) * M.toBlocks₂₂ := by
    rw [toBlocks₂₂_mul, h12, Matrix.add_mul, Matrix.mul_assoc]
  rw [Yb, e1, e2, Matrix.mul_inv_rev, mob, Matrix.mul_assoc, ← Matrix.mul_assoc M.toBlocks₂₂,
    Matrix.mul_nonsing_inv _ hu, Matrix.one_mul]

theorem Yb_mul_right {p q : ℕ} (M b : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) (hb : b.toBlocks₁₂ = 0)
    (hb2 : b.toBlocks₂₂.det ≠ 0) : Yb (M * b) = Yb M := by
  have hu : IsUnit b.toBlocks₂₂.det := isUnit_iff_ne_zero.mpr hb2
  have h0 : ∀ a j, b (Sum.inl a) (Sum.inr j) = 0 := fun a j => by
    simpa [toBlocks₁₂] using congrFun (congrFun hb a) j
  have e1 : (M * b).toBlocks₁₂ = M.toBlocks₁₂ * b.toBlocks₂₂ := by
    ext i j; simp [toBlocks₁₂, toBlocks₂₂, Matrix.mul_apply, Fintype.sum_sum_type, h0]
  have e2 : (M * b).toBlocks₂₂ = M.toBlocks₂₂ * b.toBlocks₂₂ := by
    ext i j; simp [toBlocks₂₂, Matrix.mul_apply, Fintype.sum_sum_type, h0]
  rw [Yb, Yb, e1, e2, Matrix.mul_inv_rev, Matrix.mul_assoc, ← Matrix.mul_assoc b.toBlocks₂₂,
    Matrix.mul_nonsing_inv _ hu, Matrix.one_mul]

theorem posDef_of_psd_det {n : Type*} [Fintype n] [DecidableEq n] {M : Matrix n n ℂ} (h : M.PosSemidef)
    (hd : M.det ≠ 0) : M.PosDef := by
  rw [h.1.posDef_iff_eigenvalues_pos]
  intro i
  rcases (h.eigenvalues_nonneg i).lt_or_eq with h1 | h1
  · exact h1
  · exfalso; apply hd; rw [h.1.det_eq_prod_eigenvalues]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by rw [← h1]; simp)

theorem posDef_swap {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (Y : Matrix m n ℂ) (h : (1 - Yᴴ * Y).PosDef) : (1 - Y * Yᴴ).PosDef := by
  have : Invertible (1 : Matrix m m ℂ) := invertibleOne
  have : Invertible (1 : Matrix n n ℂ) := invertibleOne
  have h1 : (fromBlocks (1 : Matrix m m ℂ) Y Yᴴ (1 : Matrix n n ℂ)).PosSemidef := by
    rw [Matrix.PosDef.fromBlocks₁₁ Y 1 Matrix.PosDef.one]; simpa using h.posSemidef
  have h2 : (1 - Y * Yᴴ).PosSemidef := by
    have := (Matrix.PosDef.fromBlocks₂₂ 1 Y Matrix.PosDef.one).mp h1; simpa using this
  refine posDef_of_psd_det h2 ?_
  rw [Matrix.det_one_sub_mul_comm]; exact (h.det_pos).ne'

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def eT (X : Data E r) : Fin (r - X.p0) ⊕ Fin X.p0 ≃ Fin r :=
  (Equiv.sumComm _ _).trans (finSumFinEquiv.trans (finCongr (by have := X.p0_le; omega)))

theorem eT_inl (X : Data E r) (j : Fin (r - X.p0)) : eT X (Sum.inl j) = ExF.qI X j := by
  ext; simp [eT, ExF.qI]

theorem eT_inr (X : Data E r) (i : Fin X.p0) : eT X (Sum.inr i) = Fin.castLE X.p0_le i := by
  ext; simp [eT]

def tl (X : Data E r) (M : Matrix (Fin r) (Fin r) ℂ) :
    Matrix (Fin (r - X.p0) ⊕ Fin X.p0) (Fin (r - X.p0) ⊕ Fin X.p0) ℂ := M.submatrix (eT X) (eT X)

theorem tl_mul (X : Data E r) (M N : Matrix (Fin r) (Fin r) ℂ) : tl X (M * N) = tl X M * tl X N := by
  rw [tl, tl, tl, Matrix.submatrix_mul_equiv]

theorem tl_nM₂₂ (X : Data E r) (z : V (nd X)) (τ : X.Ψ) : (tl X (ExF.nM X z τ)).toBlocks₂₂ = ExF.n1 X z τ := by
  ext i j; simp [tl, toBlocks₂₂, ExF.n1, eT_inr]

theorem tl_nM₁₂ (X : Data E r) (z : V (nd X)) (τ : X.Ψ) : (tl X (ExF.nM X z τ)).toBlocks₁₂ = ExF.Wm X z τ := by
  ext j i; simp [tl, toBlocks₁₂, ExF.Wm, eT_inl, eT_inr]

theorem Yb_tl_nM (X : Data E r) (z : V (nd X)) (τ : X.Ψ) : Yb (tl X (ExF.nM X z τ)) = (ExF.Zt X z τ)ᵀ := by
  rw [ExF.Zt, Matrix.transpose_transpose, Yb, tl_nM₁₂, tl_nM₂₂]

theorem tl_bor₁₂ (X : Data E r) {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) (τ : X.Ψ) :
    (tl X (mat b τ)).toBlocks₁₂ = 0 := by
  ext j i
  simp only [tl, toBlocks₁₂, Matrix.of_apply, Matrix.submatrix_apply, eT_inl, eT_inr, Matrix.zero_apply]
  apply (hb τ).2
  show (i : ℕ) < X.p0 + (j : ℕ)
  have := i.isLt; omega

theorem tl_bor₂₂ (X : Data E r) {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) (τ : X.Ψ) :
    (tl X (mat b τ)).toBlocks₂₂.det ≠ 0 := by
  have ht : (tl X (mat b τ)).toBlocks₂₂.BlockTriangular id := by
    intro i j hij
    simp only [tl, toBlocks₂₂, Matrix.of_apply, Matrix.submatrix_apply, eT_inr]
    exact (hb τ).2 _ _ (show (Fin.castLE X.p0_le j : ℕ) < Fin.castLE X.p0_le i from hij)
  rw [Matrix.det_of_isUpperTriangular ht]
  refine Finset.prod_ne_zero_iff.2 fun i _ => ?_
  simp only [tl, toBlocks₂₂, Matrix.of_apply, Matrix.submatrix_apply, eT_inr]
  exact FrameDegreeData.bdiag_ne X hb τ _

def Mx (X : Data E r) (x0 x : Frame X.Ψ r) (τ : X.Ψ) :
    Matrix (Fin (r - X.p0) ⊕ Fin X.p0) (Fin (r - X.p0) ⊕ Fin X.p0) ℂ :=
  tl X ((mat x0 τ)⁻¹ * mat x τ)

def kap (X : Data E r) (x0 : Frame X.Ψ r) (bb : ℝ) (x : Frame X.Ψ r) : ℝ :=
  ∏ τ, dpow (Yb (Mx X x0 x τ)) bb

def gm (X : Data E r) (x0 : Frame X.Ψ r) (γ : GL (Fin r) E) (τ : X.Ψ) :
    Matrix (Fin (r - X.p0) ⊕ Fin X.p0) (Fin (r - X.p0) ⊕ Fin X.p0) ℂ :=
  tl X ((mat x0 τ)⁻¹ * (γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x0 τ)

theorem Mx_rmul (X : Data E r) (x0 x b : Frame X.Ψ r) (τ : X.Ψ) :
    Mx X x0 (rmul x b) τ = Mx X x0 x τ * tl X (mat b τ) := by
  rw [Mx, Mx, ← tl_mul, Matrix.mul_assoc]; rfl

theorem kap_rmul (X : Data E r) (x0 x : Frame X.Ψ r) (bb : ℝ) {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) :
    kap X x0 bb (rmul x b) = kap X x0 bb x := by
  unfold kap
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [Mx_rmul, Yb_mul_right _ _ (tl_bor₁₂ X hb τ) (tl_bor₂₂ X hb τ)]

theorem Mx_cpt (X : Data E r) {x0 : Frame X.Ψ r} (ho : IsOrth X x0) (z : V (nd X)) (τ : X.Ψ) :
    Mx X x0 (cpt X x0 z) τ = tl X (ExF.nM X z τ) := by
  have hu : IsUnit (mat x0 τ).det := isUnit_iff_ne_zero.mpr (ExF.det_ne_of_orth X ho τ)
  rw [Mx, ExF.mat_cpt, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul]

theorem Mx_lact (X : Data E r) {x0 : Frame X.Ψ r} (ho : IsOrth X x0) (γ : GL (Fin r) E) (x : Frame X.Ψ r)
    (τ : X.Ψ) : Mx X x0 (lact γ x) τ = gm X x0 γ τ * Mx X x0 x τ := by
  have hu : IsUnit (mat x0 τ).det := isUnit_iff_ne_zero.mpr (ExF.det_ne_of_orth X ho τ)
  rw [Mx, Mx, gm, ← tl_mul]
  congr 1
  rw [Matrix.mul_assoc _ (mat x0 τ), ← Matrix.mul_assoc (mat x0 τ), Matrix.mul_nonsing_inv _ hu,
    Matrix.one_mul, Matrix.mul_assoc]; rfl

theorem det_one_sub_tr {p q : ℕ} (Z : Matrix (Fin p) (Fin q) ℂ) :
    (1 - Zᵀ * (Zᵀ)ᴴ).det = (1 - Z * Zᴴ).det := by
  rw [Matrix.det_one_sub_mul_comm]
  have : (Zᵀ)ᴴ * Zᵀ = (Z * Zᴴ)ᵀ := by
    rw [Matrix.transpose_mul]; congr 1
  rw [this, show (1 : Matrix (Fin p) (Fin p) ℂ) - (Z * Zᴴ)ᵀ = (1 - Z * Zᴴ)ᵀ by
    rw [Matrix.transpose_sub, Matrix.transpose_one], Matrix.det_transpose]

theorem kaF_eq (X : Data E r) {x0 : Frame X.Ψ r} (ho : IsOrth X x0) (bb : ℝ) {z : V (nd X)}
    (hz : z ∈ OmF X x0) : kaF X x0 bb z = kap X x0 bb (cpt X x0 z) := by
  have hpos : ∀ τ, 0 < (ExF.Am X z τ).det := fun τ => ((ExF.mem_OmF_iff X x0 ho z).1 hz τ).det_pos
  have hfac : ∀ τ, dpow (Yb (Mx X x0 (cpt X x0 z) τ)) bb = ‖(ExF.Am X z τ).det‖ ^ bb := by
    intro τ
    rw [Mx_cpt X ho, Yb_tl_nM, dpow, det_one_sub_tr, ExF.norm_of_pos (hpos τ)]; rfl
  rw [kap, Finset.prod_congr rfl (fun τ _ => hfac τ), kaF, ExF.rhF_eq_sum X x0 ho z]
  calc Real.exp (-bb * -∑ τ, Real.log ‖(ExF.Am X z τ).det‖)
      = ∏ τ, Real.exp (Real.log ‖(ExF.Am X z τ).det‖ * bb) := by
        rw [← Real.exp_sum]; congr 1; rw [neg_mul_neg, Finset.mul_sum]
        exact Finset.sum_congr rfl fun τ _ => mul_comm _ _
    _ = ∏ τ, ‖(ExF.Am X z τ).det‖ ^ bb :=
        Finset.prod_congr rfl fun τ _ => (Real.rpow_def_of_pos (norm_pos_iff.2 (hpos τ).ne') bb).symm

theorem posDef_Zt (X : Data E r) {x0 : Frame X.Ψ r} (ho : IsOrth X x0) {z : V (nd X)}
    (hz : z ∈ OmF X x0) (τ : X.Ψ) : (1 - (ExF.Zt X z τ)ᵀ * ((ExF.Zt X z τ)ᵀ)ᴴ).PosDef := by
  apply posDef_swap
  have h := ((ExF.mem_OmF_iff X x0 ho z).1 hz τ).transpose
  have : ((ExF.Zt X z τ)ᵀ)ᴴ * (ExF.Zt X z τ)ᵀ = (ExF.Zt X z τ * (ExF.Zt X z τ)ᴴ)ᵀ := by
    rw [Matrix.transpose_mul]; congr 1
  rw [this, show (1 : Matrix (Fin X.p0) (Fin X.p0) ℂ) - (ExF.Zt X z τ * (ExF.Zt X z τ)ᴴ)ᵀ =
    (1 - ExF.Zt X z τ * (ExF.Zt X z τ)ᴴ)ᵀ by rw [Matrix.transpose_sub, Matrix.transpose_one]]; exact h

end

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem herm_mat (X : Data E r) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) :
    (γ : Matrix (Fin r) (Fin r) E)ᵀ * X.Gm * (γ : Matrix (Fin r) (Fin r) E).map cc = X.Gm := by
  ext c d
  have h := (X.Γ_stab γ hγ).1 (Pi.single c 1) (Pi.single d 1)
  simp only [herm, Matrix.mulVec_single_one] at h
  have h2 : (∑ a, ∑ b, (Pi.single c (1 : E) : Fin r → E) a * X.Gm a b * cc ((Pi.single d (1 : E) : Fin r → E) b)) =
      X.Gm c d := by simp [Pi.single_apply, cc]
  rw [← h2, ← h]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  rfl

theorem gram_lact_mat (X : Data E r) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) (τ : X.Ψ)
    (M : Matrix (Fin r) (Fin r) ℂ) :
    gram τ.1 X.Gm ((γ : Matrix (Fin r) (Fin r) E).map τ.1 * M) = gram τ.1 X.Gm M := by
  have hc : ((γ : Matrix (Fin r) (Fin r) E).map τ.1).map (starRingEnd ℂ) =
      ((γ : Matrix (Fin r) (Fin r) E).map cc).map τ.1 := by
    ext a b; simp [cc, NumberField.IsCMField.complexEmbedding_complexConj]
  have key : ((γ : Matrix (Fin r) (Fin r) E).map τ.1)ᵀ * X.Gm.map τ.1 *
      ((γ : Matrix (Fin r) (Fin r) E).map τ.1).map (starRingEnd ℂ) = X.Gm.map τ.1 := by
    rw [hc, ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, herm_mat X hγ]
  rw [FrameDegreeData.gram_eq, FrameDegreeData.gram_eq, Matrix.transpose_mul, Matrix.map_mul]
  calc Mᵀ * ((γ : Matrix (Fin r) (Fin r) E).map τ.1)ᵀ * X.Gm.map τ.1 *
        (((γ : Matrix (Fin r) (Fin r) E).map τ.1).map (starRingEnd ℂ) * M.map (starRingEnd ℂ))
      = Mᵀ * (((γ : Matrix (Fin r) (Fin r) E).map τ.1)ᵀ * X.Gm.map τ.1 *
        ((γ : Matrix (Fin r) (Fin r) E).map τ.1).map (starRingEnd ℂ)) * M.map (starRingEnd ℂ) := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [key]

theorem dmin_lact (X : Data E r) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) (x : Frame X.Ψ r) (τ : X.Ψ)
    (i : Fin (r + 1)) : dmin X.Gm (lact γ x) τ i = dmin X.Gm x τ i := by
  unfold dmin
  rw [show mat (lact γ x) τ = (γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ from rfl, gram_lact_mat X hγ]

theorem lact_dom (X : Data E r) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    lact γ x ∈ X.dom := by
  intro τ
  refine ⟨?_, fun i => by rw [dmin_lact X hγ]; exact (hx τ).2 i⟩
  rw [show mat (lact γ x) τ = (γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ from rfl, Matrix.det_mul]
  refine mul_ne_zero ?_ (hx τ).1
  have hd : ((γ : Matrix (Fin r) (Fin r) E).map τ.1).det = τ.1 (γ : Matrix (Fin r) (Fin r) E).det := by
    rw [RingHom.map_det]; rfl
  rw [hd]
  exact (map_ne_zero τ.1).2 (Matrix.GeneralLinearGroup.det_ne_zero γ)

theorem lact_lact (X : Data E r) (a b : GL (Fin r) E) (x : Frame X.Ψ r) :
    lact a (lact b x) = lact (a * b) x := by
  funext τ
  show ((a : Matrix (Fin r) (Fin r) E).map τ.1 * ((b : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ) :
    Matrix (Fin r) (Fin r) ℂ) = ((a * b : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ
  rw [Units.val_mul, Matrix.map_mul, Matrix.mul_assoc]

theorem lact_one (X : Data E r) (x : Frame X.Ψ r) : lact (1 : GL (Fin r) E) x = x := by
  funext τ
  show (((1 : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ : Matrix (Fin r) (Fin r) ℂ) = x τ
  rw [Units.val_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]; rfl

theorem cpt_lact (X : Data E r) (γ : GL (Fin r) E) (x0 : Frame X.Ψ r) (z : V (nd X)) :
    cpt X (lact γ x0) z = lact γ (cpt X x0 z) := by
  funext τ
  show (((γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x0 τ) * mat (nmat X z) τ : Matrix (Fin r) (Fin r) ℂ) =
    (γ : Matrix (Fin r) (Fin r) E).map τ.1 * (mat x0 τ * mat (nmat X z) τ)
  rw [Matrix.mul_assoc]

theorem isOrth_lact (X : Data E r) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) {x0 : Frame X.Ψ r} (ho : IsOrth X x0) :
    IsOrth X (lact γ x0) := fun τ => by
  rw [show mat (lact γ x0) τ = (γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x0 τ from rfl, gram_lact_mat X hγ]
  exact ho τ

theorem OmF_lact (X : Data E r) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) (x0 : Frame X.Ψ r) :
    OmF X (lact γ x0) = OmF X x0 := by
  ext z
  simp only [OmF, Set.mem_ofPred_eq, cpt_lact]
  refine ⟨fun h => ?_, lact_dom X hγ⟩
  have := lact_dom X (X.Γ.inv_mem hγ) h
  rwa [lact_lact, inv_mul_cancel, lact_one] at this

theorem muF_lact (X : Data E r) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) (x0 : Frame X.Ψ r) :
    muF X (lact γ x0) = muF X x0 := by
  have hd : (fun z => ENNReal.ofReal (densF X (lact γ x0) z)) = fun z => ENNReal.ofReal (densF X x0 z) := by
    funext z; simp only [densF, cpt_lact, dmin_lact X hγ]
  rw [muF, muF, OmF_lact X hγ, hd]

theorem tl_D (X : Data E r) :
    tl X (Matrix.diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)) = -Jf (r - X.p0) X.p0 := by
  ext a b
  rcases a with j | i <;> rcases b with j' | i'
  · simp only [tl, Matrix.submatrix_apply, eT_inl, Jf, Matrix.neg_apply, Matrix.fromBlocks_apply₁₁,
      Matrix.diagonal_apply, Matrix.one_apply, ExF.qI, Fin.ext_iff, Nat.add_left_cancel_iff]
    split_ifs <;> simp [sgn]
  · simp only [tl, Matrix.submatrix_apply, eT_inl, eT_inr, Jf, Matrix.neg_apply, Matrix.fromBlocks_apply₁₂,
      Matrix.diagonal_apply, ExF.qI, Fin.ext_iff, Fin.coe_castLE, Matrix.zero_apply, neg_zero]
    rw [if_neg]; have := i'.isLt; omega
  · simp only [tl, Matrix.submatrix_apply, eT_inl, eT_inr, Jf, Matrix.neg_apply, Matrix.fromBlocks_apply₂₁,
      Matrix.diagonal_apply, ExF.qI, Fin.ext_iff, Fin.coe_castLE, Matrix.zero_apply, neg_zero]
    rw [if_neg]; have := i.isLt; omega
  · simp only [tl, Matrix.submatrix_apply, eT_inr, Jf, Matrix.neg_apply, Matrix.fromBlocks_apply₂₂,
      Matrix.diagonal_apply, Matrix.neg_apply, Matrix.one_apply, Fin.ext_iff, Fin.coe_castLE, neg_neg]
    split_ifs with h <;> simp [sgn, i.isLt]

theorem gm_upq (X : Data E r) {x0 : Frame X.Ψ r} (ho : IsOrth X x0) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ)
    (τ : X.Ψ) : IsUpq (gm X x0 γ τ) := by
  set A := (γ : Matrix (Fin r) (Fin r) E).map τ.1 with hA
  set x := mat x0 τ with hx
  set m := x⁻¹ * A * x with hm
  set D := Matrix.diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ) with hD
  have hu : IsUnit x.det := isUnit_iff_ne_zero.mpr (ExF.det_ne_of_orth X ho τ)
  have hxm : x * m = A * x := by
    rw [hm, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.one_mul]
  have h1 : mᵀ * D * m.map (starRingEnd ℂ) = D := by
    have := FrameDegreeData.gram_mul τ.1 X.Gm x m
    rw [hxm, gram_lact_mat X hγ, ho τ] at this; exact this.symm
  have h2 : mᴴ * D * m = D := by
    have := congrArg (fun M => M.map (starRingEnd ℂ)) h1
    have e1 : (mᵀ).map (starRingEnd ℂ) = mᴴ := by ext; simp [Matrix.conjTranspose_apply]
    have e2 : D.map (starRingEnd ℂ) = D := by
      ext a b; simp only [hD, Matrix.map_apply, Matrix.diagonal_apply]; split_ifs <;> simp
    have e3 : (m.map (starRingEnd ℂ)).map (starRingEnd ℂ) = m := by ext; simp
    simp only [Matrix.map_mul] at this
    rwa [e1, e2, e3] at this
  have h3 : (tl X m)ᴴ * tl X D * tl X m = tl X D := by
    rw [show (tl X m)ᴴ = tl X mᴴ from Matrix.conjTranspose_submatrix _ _ _, ← tl_mul, ← tl_mul, h2]
  rw [hD, tl_D, Matrix.mul_neg, Matrix.neg_mul, neg_inj] at h3
  exact h3

end

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.KU
