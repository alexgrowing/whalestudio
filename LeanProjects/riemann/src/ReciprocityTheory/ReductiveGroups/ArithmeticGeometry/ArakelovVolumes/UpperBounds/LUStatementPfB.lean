import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LUStatementPfA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ExtFStatementPfA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.LminorSubmatrixCastSucc

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf

open Matrix NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf

noncomputable section

def LowU {n : ℕ} (N : Matrix (Fin n) (Fin n) ℂ) : Prop := (∀ i k : Fin n, i < k → N i k = 0) ∧ ∀ i, N i i = 1

theorem LowU.det {n : ℕ} {N : Matrix (Fin n) (Fin n) ℂ} (h : LowU N) : N.det = 1 := by
  have hbt : N.BlockTriangular OrderDual.toDual := by
    intro i j hij
    exact h.1 i j (OrderDual.toDual_lt_toDual.mp hij)
  rw [Matrix.det_of_lowerTriangular N hbt]
  simp [h.2]

theorem LowU.inv {n : ℕ} {N : Matrix (Fin n) (Fin n) ℂ} (h : LowU N) : LowU N⁻¹ := by
  have hd : IsUnit N.det := by rw [h.det]; exact isUnit_one
  have hbt : N.BlockTriangular OrderDual.toDual := by
    intro i j hij
    exact h.1 i j (OrderDual.toDual_lt_toDual.mp hij)
  letI : Invertible N := N.invertibleOfIsUnitDet hd
  have hinv : N⁻¹.BlockTriangular OrderDual.toDual := Matrix.blockTriangular_inv_of_blockTriangular hbt
  refine ⟨fun i k hik => hinv (OrderDual.toDual_lt_toDual.mpr hik), fun i => ?_⟩
  have h1 : (N * N⁻¹) i i = 1 := by rw [Matrix.mul_nonsing_inv N hd]; simp
  rw [Matrix.mul_apply, Finset.sum_eq_single i] at h1
  · simpa [h.2] using h1
  · intro j _ hji
    rcases lt_or_gt_of_ne hji with hlt | hlt
    · rw [hinv (OrderDual.toDual_lt_toDual.mpr hlt), mul_zero]
    · rw [h.1 i j hlt, zero_mul]
  · simp

theorem Lm_lowU {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) : LowU (Lm M) := by
  refine ⟨fun i k hik => ?_, fun i => by simp [Lm]⟩
  have h1 : ¬ ((k : ℕ) < i) := by rw [Fin.lt_iff_val_lt_val] at hik; omega
  simp only [Lm, Matrix.of_apply]
  rw [dif_neg h1, if_neg (ne_of_gt hik)]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) (x0 : Frame X.Ψ r)

theorem orthogonalFrame_det_ne_zero (hx0 : IsOrth X x0) (τ : X.Ψ) : (mat x0 τ).det ≠ 0 := by
  intro h
  have hg := hx0 τ
  have key : ReciprocityTheory.ChartRestriction.G.FD.gram (↑τ) X.Gm (mat x0 τ) =
      (mat x0 τ).transpose * X.Gm.map (↑τ : E →+* ℂ) * (mat x0 τ).map (starRingEnd ℂ) := by
    ext a b
    simp only [ReciprocityTheory.ChartRestriction.G.FD.gram, ReciprocityTheory.ChartRestriction.G.FD.hermC, ReciprocityTheory.ChartRestriction.G.FD.col, Matrix.of_apply,
      Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
    exact Finset.sum_comm
  have hd := congrArg Matrix.det hg
  rw [key, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, h, zero_mul, zero_mul,
    Matrix.det_diagonal] at hd
  exact absurd hd.symm (Finset.prod_ne_zero_iff.mpr fun a _ => by
    unfold ReciprocityTheory.ChartRestriction.G.FD.sgn; split_ifs <;> norm_num)

def Mx (x : Frame X.Ψ r) (τ : X.Ψ) : Matrix (Fin r) (Fin r) ℂ := (mat x0 τ)⁻¹ * mat x τ

def DeltaF (x : Frame X.Ψ r) : ℂ := ∏ τ, ∏ k : Fin (r + 1), lminor (Mx X x0 x τ) k

def nF (x : Frame X.Ψ r) : Frame X.Ψ r := fun τ => ((Lm (Mx X x0 x τ))⁻¹ : Matrix (Fin r) (Fin r) ℂ)

def bF (x : Frame X.Ψ r) : Frame X.Ψ r := fun τ => (Lm (Mx X x0 x τ) * Mx X x0 x τ : Matrix (Fin r) (Fin r) ℂ)

def zF (x : Frame X.Ψ r) : V (nd X) :=
  WithLp.toLp 2 fun k => nF X x0 x ((Fintype.equivFin (Ent X)).symm k).1
    ((Fintype.equivFin (Ent X)).symm k).2.1.1 ((Fintype.equivFin (Ent X)).symm k).2.1.2

theorem nmat_lowU (z : V (nd X)) (τ : X.Ψ) : LowU (mat (nmat X z) τ) := by
  unfold nmat
  refine ⟨fun i k hik => ?_, fun i => ?_⟩
  · simp only [mat, Matrix.of_apply]
    rw [dif_neg (not_lt.mpr hik.le), if_neg (ne_of_lt hik)]
  · simp [mat]

theorem nmat_eq_of (z : V (nd X)) (n : Frame X.Ψ r) (hn : ∀ τ, LowU (mat n τ))
    (hz : ∀ (τ : X.Ψ) (a c : Fin r) (h : c < a), z ((Fintype.equivFin (Ent X)) ⟨τ, ⟨(a, c), h⟩⟩) = n τ a c) :
    nmat X z = n := by
  funext τ a c
  have h1 := (hn τ).1 a c
  have h2 := (hn τ).2 a
  simp only [mat, Matrix.of_apply] at h1 h2
  unfold nmat
  split_ifs with h h'
  · exact hz τ a c h
  · subst h'
    exact h2.symm
  · exact (h1 (lt_of_le_of_ne (not_lt.mp h) h')).symm

variable {X x0}

theorem Mx_rmul (hx0 : IsOrth X x0) (z : V (nd X)) (b : Frame X.Ψ r) (τ : X.Ψ) :
    Mx X x0 (rmul (cpt X x0 z) b) τ = mat (nmat X z) τ * mat b τ := by
  show (mat x0 τ)⁻¹ * (mat x0 τ * mat (nmat X z) τ * mat b τ) = mat (nmat X z) τ * mat b τ
  have hu : IsUnit (mat x0 τ).det := (orthogonalFrame_det_ne_zero X x0 hx0 τ).isUnit
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul]

theorem lminors_ne {x : Frame X.Ψ r} (hΔ : DeltaF X x0 x ≠ 0) (τ : X.Ψ) (k : Fin (r + 1)) :
    lminor (Mx X x0 x τ) k ≠ 0 := by
  unfold DeltaF at hΔ
  rw [Finset.prod_ne_zero_iff] at hΔ
  have h1 := hΔ τ (Finset.mem_univ _)
  rw [Finset.prod_ne_zero_iff] at h1
  exact h1 k (Finset.mem_univ _)

private lemma Lm_mul_apply_eq_zero_of_lt {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (i k : Fin n) (hki : k < i)
    (hdet : (lb M i).det ≠ 0) : (Lm M * M) i k = 0 := by
  have hkey : ∑ j : Fin i, wv M i j * M (Fin.castLE i.isLt.le j) k = M i k := by
    have h1 : vecMul (wv M i) (lb M i) = fun j : Fin i => M i (Fin.castLE i.isLt.le j) := by
      unfold wv
      rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet), Matrix.vecMul_one]
    have h2 := congrFun h1 ⟨k.1, hki⟩
    simp only [Matrix.vecMul, dotProduct, Matrix.submatrix_apply] at h2
    exact h2
  have hf : ∀ j : Fin n, Lm M i j * M j k =
      (if h : (j : ℕ) < i then -wv M i ⟨j, h⟩ * M j k else 0) + (if j = i then M j k else 0) := by
    intro j
    simp only [Lm, Matrix.of_apply]
    by_cases h : (j : ℕ) < i
    · have hne : j ≠ i := fun e => by rw [e] at h; exact lt_irrefl _ h
      rw [dif_pos h, dif_pos h, if_neg hne]
      ring
    · rw [dif_neg h, dif_neg h]
      by_cases e : j = i
      · rw [if_pos e, if_pos e]
        ring
      · rw [if_neg e, if_neg e]
        ring
  have hg : ∑ j : Fin n, (if h : (j : ℕ) < i then -wv M i ⟨j, h⟩ * M j k else 0) =
      ∑ j : Fin i, -wv M i j * M (Fin.castLE i.isLt.le j) k := by
    symm
    apply Finset.sum_of_injOn (Fin.castLE i.isLt.le)
    · exact (Fin.castLE_injective _).injOn
    · intro _ _
      exact Finset.mem_coe.mpr (Finset.mem_univ _)
    · intro j _ hj
      rw [dif_neg]
      intro hlt
      exact hj ⟨⟨j.1, hlt⟩, Finset.mem_coe.mpr (Finset.mem_univ _), Fin.ext rfl⟩
    · intro j _
      split_ifs with h
      · rfl
      · exact absurd j.isLt h
  rw [Matrix.mul_apply, Finset.sum_congr rfl fun j _ => hf j, Finset.sum_add_distrib, hg,
    Finset.sum_ite_eq' Finset.univ i, if_pos (Finset.mem_univ _), ← hkey]
  simp only [neg_mul, Finset.sum_neg_distrib, neg_add_cancel]

theorem bF_mem {x : Frame X.Ψ r} (_hx : x ∈ X.dom) (hΔ : DeltaF X x0 x ≠ 0) : bF X x0 x ∈ Bor X.Ψ r := by
  show ∀ τ : X.Ψ, (mat (bF X x0 x) τ).det ≠ 0 ∧ ∀ a c : Fin r, c < a → bF X x0 x τ a c = 0
  intro τ
  have hM := lminors_ne hΔ τ
  refine ⟨?_, fun a c hca => ?_⟩
  · show (Lm (Mx X x0 x τ) * Mx X x0 x τ).det ≠ 0
    rw [Matrix.det_mul, (Lm_lowU _).det, one_mul]
    exact hM (Fin.last r)
  · show (Lm (Mx X x0 x τ) * Mx X x0 x τ) a c = 0
    exact Lm_mul_apply_eq_zero_of_lt _ a c hca (hM a.castSucc)

theorem nmat_zF (x : Frame X.Ψ r) : nmat X (zF X x0 x) = nF X x0 x := by
  refine nmat_eq_of X (zF X x0 x) (nF X x0 x) (fun τ => ?_) (fun τ a c h => ?_)
  · show LowU ((Lm (Mx X x0 x τ))⁻¹)
    exact (Lm_lowU _).inv
  · simp [zF]

theorem split_eq (hx0 : IsOrth X x0) (x : Frame X.Ψ r) :
    x = rmul (cpt X x0 (zF X x0 x)) (bF X x0 x) := by
  funext τ
  have hu0 : IsUnit (mat x0 τ).det := (orthogonalFrame_det_ne_zero X x0 hx0 τ).isUnit
  have hL : IsUnit (Lm (Mx X x0 x τ)).det := by rw [(Lm_lowU _).det]; exact isUnit_one
  show mat x τ = (mat x0 τ * mat (nmat X (zF X x0 x)) τ) * mat (bF X x0 x) τ
  rw [nmat_zF]
  show mat x τ = (mat x0 τ * (Lm (Mx X x0 x τ))⁻¹) * (Lm (Mx X x0 x τ) * ((mat x0 τ)⁻¹ * mat x τ))
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc (Lm (Mx X x0 x τ))⁻¹, Matrix.nonsing_inv_mul _ hL, Matrix.one_mul,
    ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu0, Matrix.one_mul]

theorem zF_mem (hx0 : IsOrth X x0) {x : Frame X.Ψ r} (hx : x ∈ X.dom) (hΔ : DeltaF X x0 x ≠ 0) :
    zF X x0 x ∈ OmF X x0 := by
  have hb := bF_mem hx hΔ
  have hsplit := split_eq hx0 x
  show cpt X x0 (zF X x0 x) ∈ X.dom
  have h1 : cpt X x0 (zF X x0 x) = rmul x (ExtFPf.invF X (bF X x0 x)) := by
    calc cpt X x0 (zF X x0 x)
        = rmul (rmul (cpt X x0 (zF X x0 x)) (bF X x0 x)) (ExtFPf.invF X (bF X x0 x)) := by
          rw [ExtFPf.rmul_assoc X, ExtFPf.rmul_invF X hb, ExtFPf.rmul_oneF X]
      _ = rmul x (ExtFPf.invF X (bF X x0 x)) := by rw [← hsplit]
  rw [h1]
  exact OrthogonalFrameDomain.rmul_mem_dom X hx (ExtFPf.invF_mem X hb)

theorem uniq_all (hx0 : IsOrth X x0) {z : V (nd X)} {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) :
    DeltaF X x0 (rmul (cpt X x0 z) b) ≠ 0 ∧ zF X x0 (rmul (cpt X x0 z) b) = z ∧
      bF X x0 (rmul (cpt X x0 z) b) = b := by
  have hdet : ∀ τ, IsUnit (mat (nmat X z) τ).det := fun τ => by
    rw [(nmat_lowU X z τ).det]
    exact isUnit_one
  have key : ∀ τ, Lm (Mx X x0 (rmul (cpt X x0 z) b) τ) = (mat (nmat X z) τ)⁻¹ ∧
      ∀ k, lminor (Mx X x0 (rmul (cpt X x0 z) b) τ) k ≠ 0 := by
    intro τ
    have hN := nmat_lowU X z τ
    have hB : (mat b τ).BlockTriangular id := (ExtFPf.upper_iff X b τ).mp (hb τ).2
    have hdiag : ∀ i, mat b τ i i ≠ 0 := by
      intro i h0
      apply (hb τ).1
      rw [Matrix.det_of_upperTriangular hB]
      exact Finset.prod_eq_zero (Finset.mem_univ i) h0
    rw [Mx_rmul hx0 z b τ]
    have hmin : ∀ k, lminor (mat (nmat X z) τ * mat b τ) k ≠ 0 := by
      intro k
      rw [lminor_nb _ _ hN.1 hN.2 hB k]
      exact Finset.prod_ne_zero_iff.mpr fun j _ => hdiag _
    refine ⟨?_, hmin⟩
    symm
    apply Lm_unique _ _ hmin hN.inv.1 hN.inv.2
    intro i j hji
    rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (hdet τ), Matrix.one_mul]
    exact hB hji
  refine ⟨?_, ?_, ?_⟩
  · unfold DeltaF
    exact Finset.prod_ne_zero_iff.mpr fun τ _ => Finset.prod_ne_zero_iff.mpr fun k _ => (key τ).2 k
  · have hn : nF X x0 (rmul (cpt X x0 z) b) = nmat X z := by
      funext τ
      show ((Lm (Mx X x0 (rmul (cpt X x0 z) b) τ))⁻¹ : Matrix (Fin r) (Fin r) ℂ) = mat (nmat X z) τ
      rw [(key τ).1, Matrix.nonsing_inv_nonsing_inv _ (hdet τ)]
    have h2 := nmat_zF (X := X) (x0 := x0) (rmul (cpt X x0 z) b)
    rw [hn] at h2
    ext k
    have heta : (⟨((Fintype.equivFin (Ent X)).symm k).1, ⟨(((Fintype.equivFin (Ent X)).symm k).2.1.1,
        ((Fintype.equivFin (Ent X)).symm k).2.1.2), ((Fintype.equivFin (Ent X)).symm k).2.2⟩⟩ : Ent X) =
        (Fintype.equivFin (Ent X)).symm k := rfl
    have h3 := congrFun (congrFun (congrFun h2 ((Fintype.equivFin (Ent X)).symm k).1)
      ((Fintype.equivFin (Ent X)).symm k).2.1.1) ((Fintype.equivFin (Ent X)).symm k).2.1.2
    simp only [nmat, dif_pos ((Fintype.equivFin (Ent X)).symm k).2.2, heta] at h3
    have h4 : (Fintype.equivFin (Ent X)) ((Fintype.equivFin (Ent X)).symm k) = k :=
      Equiv.apply_symm_apply _ _
    rwa [h4] at h3
  · funext τ
    show Lm (Mx X x0 (rmul (cpt X x0 z) b) τ) * Mx X x0 (rmul (cpt X x0 z) b) τ = mat b τ
    rw [(key τ).1, Mx_rmul hx0 z b τ, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (hdet τ), Matrix.one_mul]

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf
