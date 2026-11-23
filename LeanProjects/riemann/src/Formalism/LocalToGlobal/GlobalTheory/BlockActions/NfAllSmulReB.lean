import Formalism.LocalToGlobal.GlobalTheory.BlockActions.ExistsOnOfPosDef
import Formalism.LocalToGlobal.GlobalTheory.NfAllSmulSelfRe

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Br

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms Matrix Formalism.UG

section Gen

variable {ι : Type} [Fintype ι] {n : ℕ}

theorem fnOf_trG (G : ι → Matrix (Fin n) (Fin n) ℂ) (s : ι → ℤ) (M g : ι → Matrix (Fin n) (Fin n) ℂ)
    (hg : ∀ τ, IsUnit (g τ).det) (P : MvPolynomial (ι × Fin n × Fin n) ℂ) (y : Frames G) :
    fnOf G s M P (y.tr g hg) = fnOf G s (fun τ => M τ * g τ) P y := by
  simp only [fnOf, LinearMap.coe_mk, AddHom.coe_mk, Frames.tr, Matrix.mul_assoc]

end Gen

variable {D : D7} {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i}

theorem shift_lamTr : shiftOf (lamT u D.R.m) = fun τ => (lamTr D u τ).detShift := by
  funext τ
  have hk := D.R.m_add_three_le_k
  have hN : D.R.N D.R.m = D.R.k + D.R.m * (D.R.t + 1) := rfl
  have h1 : 0 < D.R.N D.R.m := by omega
  simp only [shiftOf, lamT, lamTr]
  rw [detShift_shW _ _ h1, detShift_wSh _ _ h1]
  rfl

theorem cspan_lamTr : Formalism.MainNotions.product_first_zeroth_parts.CSpan (lamTr D u) = Formalism.MainNotions.product_first_zeroth_parts.CSpan ((D.fm u).lam D.R.m) := by
  simp only [Formalism.MainNotions.product_first_zeroth_parts.CSpan, lamTr, delSq_wSh]

set_option maxHeartbeats 1000000 in

theorem val_of_trEv (Tf : FormsTiedSym D u Ch chOf) (c : (D.fm u).clsP) (f : (D.mem u).C.Y D.R.m → ℂ)
    (M : D.what₂.Tau → Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) ℂ) (Q : MvPolynomial (D.what₂.Tau × Fin (D.R.N D.R.m) × Fin (D.R.N D.R.m)) ℂ)
    (hq : trEvS Tf c f = fnOf _ (shiftOf (lamT u D.R.m)) M Q) (z : (D.mem u).C.Y D.R.m) :
    f z = fnOf _ (shiftOf (lamT u D.R.m))
      (fun τ => M τ * atInf (embT D) (((Tf.til.ga c).1 : GL (Fin (D.R.N D.R.m)) D.host.E) : Matrix _ _ D.host.E) τ)
      ((((Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.chi (Tf.tilAd.ka c) : ℂˣ) : ℂ) • Q) ((Tf.val D.R.m le_rfl (Or.inr rfl)).eY z) := by
  let ga : GL (Fin (D.R.N D.R.m)) D.host.E := (Tf.til.ga c).1
  have hy := congrFun hq (((Tf.val D.R.m le_rfl (Or.inr rfl)).eY z).tr (atInf (embT D) (ga : Matrix _ _ D.host.E))
    (isUnit_det_atInf (embT D) ga))
  have hback : (((Tf.val D.R.m le_rfl (Or.inr rfl)).eY z).tr (atInf (embT D) (ga : Matrix _ _ D.host.E))
      (isUnit_det_atInf (embT D) ga)).tr (atInf (embT D) ((ga⁻¹ : GL (Fin (D.R.N D.R.m)) D.host.E) : Matrix _ _ D.host.E))
      (isUnit_det_atInf (embT D) ga⁻¹) = (Tf.val D.R.m le_rfl (Or.inr rfl)).eY z := by
    apply Subtype.ext
    funext τ
    show atInf (embT D) ((ga⁻¹ : GL (Fin (D.R.N D.R.m)) D.host.E) : Matrix _ _ D.host.E) τ *
      (atInf (embT D) (ga : Matrix _ _ D.host.E) τ * ((Tf.val D.R.m le_rfl (Or.inr rfl)).eY z).1 τ) =
        ((Tf.val D.R.m le_rfl (Or.inr rfl)).eY z).1 τ
    have h1 := atInf_mul_inv (embT D) ga⁻¹ τ
    rw [inv_inv] at h1
    rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  simp only [trEvS, LinearMap.smul_apply, LinearMap.funLeft_apply, Pi.smul_apply, smul_eq_mul] at hy
  rw [hback, Equiv.symm_apply_apply, fnOf_trG] at hy
  rw [map_smul, Pi.smul_apply, smul_eq_mul, ← hy, ← mul_assoc, Units.mul_inv, one_mul]

section Frame

variable (D) in

abbrev eN : Fin (D.R.N D.R.m - 1) ⊕ Fin 1 ≃ Fin (D.R.N D.R.m) := finSumFinEquiv.trans (finCongr (Nm_succ D.R))

theorem lastGL_eq (a : ℂˣ) : ((Formalism.MainNotions.PrimeDegreeVariant.lastGL ℂ (D.R.N D.R.m) a : GL (Fin (D.R.N D.R.m)) ℂ) : Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) ℂ) =
    Matrix.reindex (eN D) (eN D) (Matrix.fromBlocks 1 0 0 (Matrix.of fun _ _ => (a : ℂ))) := by
  have hN := Nm_succ D.R
  ext x y
  obtain ⟨p, rfl⟩ := (eN D).surjective x
  obtain ⟨q, rfl⟩ := (eN D).surjective y
  rw [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  show Matrix.diagonal _ _ _ = _
  rcases p with i | i <;> rcases q with j | j
  · have hi' : ¬ ((i : ℕ) + 1 = D.R.N D.R.m) := by have := i.isLt; omega
    by_cases hij : i = j
    · subst hij; simp [Matrix.diagonal_apply, hi']
    · have hne : (eN D) (Sum.inl i) ≠ (eN D) (Sum.inl j) := fun h => hij (Sum.inl_injective ((eN D).injective h))
      simp [Matrix.diagonal_apply, hne, Matrix.one_apply, hij]
  · have := i.isLt
    simp [Matrix.diagonal_apply, Fin.ext_iff]; omega
  · have := j.isLt
    simp [Matrix.diagonal_apply, Fin.ext_iff]; omega
  · have hi : i = 0 := Subsingleton.elim _ _
    have hj : j = 0 := Subsingleton.elim _ _
    subst hi hj
    simp [Matrix.diagonal_apply, hN]

def dOT (u : D.what₂.Word) (o' : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) ℂ) :
    Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) ℂ :=
  Matrix.reindex (eN D) (eN D) (Matrix.fromBlocks o' 0 0 (Matrix.of fun _ _ => ((sqrtT D u : ℂˣ) : ℂ)))

theorem reindex_mulB {a b : Type} [Fintype a] [Fintype b] {c : Type} [Semiring c] (e : a ≃ b) (X Y : Matrix a a c) :
    Matrix.reindex e e X * Matrix.reindex e e Y = Matrix.reindex e e (X * Y) := by
  simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv]

theorem sqrtT_mul_self : ((sqrtT D u : ℂˣ) : ℂ) * ((sqrtT D u : ℂˣ) : ℂ) = ((D.mem u).A.T : ℂ) := by
  simp only [sqrtT, Units.val_mk0]
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg _)]
  push_cast; rfl

theorem star_sqrtT : star ((sqrtT D u : ℂˣ) : ℂ) = ((sqrtT D u : ℂˣ) : ℂ) := by
  simp only [sqrtT, Units.val_mk0, Complex.star_def, Complex.conj_ofReal]

theorem dgE_map (B' : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E) (τ : D.what₂.Tau) :
    (dgE B').map (embT D τ) = Matrix.reindex (eN D) (eN D) (Matrix.fromBlocks (B'.map (embT D τ)) 0 0 1) := by
  unfold dgE
  rw [Matrix.reindex_apply, Matrix.reindex_apply, ← Matrix.submatrix_map, Matrix.fromBlocks_map,
    Matrix.map_zero _ (map_zero _), Matrix.map_zero _ (map_zero _), Matrix.map_one _ (map_zero _) (map_one _)]

theorem dgE_gFull (B' : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E) (hB' : IsUnit B'.det)
    (o' : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) ℂ) (τ : D.what₂.Tau) (g : GL (Fin (D.R.N D.R.m - 1)) ℂ)
    (hg : (g : Matrix _ _ ℂ) = (atInf (embT D) B'⁻¹ τ * o')ᵀ) :
    (dgE B').map (embT D τ) * ((gFull D u g : GL (Fin (D.R.N D.R.m)) ℂ) : Matrix _ _ ℂ)ᵀ = dOT u o' := by
  have hl : ((Formalism.MainNotions.PrimeDegreeVariant.lastGL ℂ (D.R.N D.R.m) (sqrtT D u) : GL _ ℂ) : Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) ℂ)ᵀ =
      Matrix.reindex (eN D) (eN D) (Matrix.fromBlocks 1 0 0 (Matrix.of fun _ _ => ((sqrtT D u : ℂˣ) : ℂ))) := by
    rw [← lastGL_eq]
    show (Matrix.diagonal _)ᵀ = Matrix.diagonal _
    exact Matrix.diagonal_transpose _
  have he : ((Formalism.MainNotions.PrimeDegreeVariant.embGL ℂ _ _ (Nm_succ D.R) g : GL (Fin (D.R.N D.R.m)) ℂ) : Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) ℂ)ᵀ =
      Matrix.reindex (eN D) (eN D) (Matrix.fromBlocks (atInf (embT D) B'⁻¹ τ * o') 0 0 1) := by
    rw [embGL_val, Matrix.transpose_reindex, Matrix.fromBlocks_transpose, hg, Matrix.transpose_transpose,
      Matrix.transpose_zero, Matrix.transpose_zero, Matrix.transpose_one]
  have hBB : B'.map (embT D τ) * atInf (embT D) B'⁻¹ τ = 1 := by
    show B'.map (embT D τ) * (B'⁻¹).map (embT D τ) = 1
    rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ hB', Matrix.map_one _ (map_zero _) (map_one _)]
  unfold gFull
  rw [Units.val_mul, Matrix.transpose_mul, hl, he, dgE_map, reindex_mulB, reindex_mulB, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_multiply]
  unfold dOT
  congr 1
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one, Matrix.one_mul, ← Matrix.mul_assoc, hBB]

theorem dOT_on (o' G' : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) ℂ) (ho : o'ᴴ * G' * o' = 1) :
    (dOT u o')ᴴ * Matrix.reindex (eN D) (eN D) (Matrix.fromBlocks G' 0 0 (Matrix.of fun _ _ => ((D.mem u).A.T : ℂ)⁻¹)) *
      dOT u o' = 1 := by
  have hT : ((D.mem u).A.T : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (D.mem u).A.T_prime.ne_zero
  unfold dOT
  rw [Matrix.conjTranspose_reindex, Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_zero, Matrix.conjTranspose_zero,
    reindex_mulB, reindex_mulB, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  rw [show (1 : Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) ℂ) = Matrix.reindex (eN D) (eN D) 1 by
    rw [Matrix.reindex_apply, Matrix.submatrix_one_equiv]]
  congr 1
  rw [← Matrix.fromBlocks_one]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, ho]
  congr 1
  ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Fin.sum_univ_one, Matrix.one_apply, Fin.fin_one_eq_zero,
    if_true, star_sqrtT]
  rw [show ((sqrtT D u : ℂˣ) : ℂ) * ((D.mem u).A.T : ℂ)⁻¹ * ((sqrtT D u : ℂˣ) : ℂ) =
    ((sqrtT D u : ℂˣ) : ℂ) * ((sqrtT D u : ℂˣ) : ℂ) * ((D.mem u).A.T : ℂ)⁻¹ by ring, sqrtT_mul_self, mul_inv_cancel₀ hT]

end Frame

section Main

theorem ga_inv_unitary (Tf : FormsTiedSym D u Ch chOf) (c : (D.fm u).clsP) (τ : D.what₂.Tau) :
    (atInf (embT D) ((((Tf.til.ga c).1)⁻¹ : GL (Fin (D.R.N D.R.m)) D.host.E) : Matrix _ _ D.host.E) τ)ᴴ *
      gramC (gramN D D.R.m le_rfl) (embT D) τ *
      atInf (embT D) ((((Tf.til.ga c).1)⁻¹ : GL (Fin (D.R.N D.R.m)) D.host.E) : Matrix _ _ D.host.E) τ =
      gramC (gramN D D.R.m le_rfl) (embT D) τ := by
  have h := ((Tf.til.ga c)⁻¹).2
  rw [InvMemClass.coe_inv] at h
  have h' : (((((Tf.til.ga c).1)⁻¹ : GL (Fin (D.R.N D.R.m)) D.host.E) : Matrix _ _ D.host.E).map
      (sigD D : D.host.E →+* D.host.E))ᵀ * gramN D D.R.m le_rfl *
      ((((Tf.til.ga c).1)⁻¹ : GL (Fin (D.R.N D.R.m)) D.host.E) : Matrix _ _ D.host.E) = gramN D D.R.m le_rfl := h
  have h2 := congrArg (fun X => X.map (embT D τ)) h'
  simp only [Matrix.map_mul] at h2
  rw [map_cT] at h2
  exact h2

theorem gram_bZ_map (Tf : FormsTiedSym D u Ch chOf) (τ : D.what₂.Tau) :
    (atInf (embT D) (bZ u Tf.til.z0) τ)ᴴ * gramC (gramN D D.R.m le_rfl) (embT D) τ * atInf (embT D) (bZ u Tf.til.z0) τ =
      Matrix.reindex (eN D) (eN D) (Matrix.fromBlocks (gramC (gramP D) (embT D) τ) 0 0
        (Matrix.of fun _ _ => ((D.mem u).A.T : ℂ)⁻¹)) := by
  have h := gram_bZ (u := u) Tf.til.z0 Tf.til.lastCoordinateUniformizerVector_spans_orthogonal_line Tf.til.hermitianForm_lastCoordinateUniformizerVector_self
  have h2 := congrArg (fun X => X.map (embT D τ)) h
  simp only [Matrix.map_mul] at h2
  rw [map_cT] at h2
  show ((bZ u Tf.til.z0).map (embT D τ))ᴴ * (gramN D D.R.m le_rfl).map (embT D τ) * (bZ u Tf.til.z0).map (embT D τ) = _
  rw [h2, Matrix.reindex_apply, Matrix.reindex_apply, ← Matrix.submatrix_map, Matrix.fromBlocks_map,
    Matrix.map_zero _ (map_zero _), Matrix.map_zero _ (map_zero _)]
  congr 2
  ext i j
  simp [gramC, map_inv₀, map_natCast]

theorem frame_on (Tf : FormsTiedSym D u Ch chOf) (c : (D.fm u).clsP) (τ : D.what₂.Tau)
    (o' : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) ℂ) (ho : o'ᴴ * gramC (gramP D) (embT D) τ * o' = 1) :
    (atInf (embT D) ((((Tf.til.ga c).1)⁻¹ : GL (Fin (D.R.N D.R.m)) D.host.E) : Matrix _ _ D.host.E) τ *
        atInf (embT D) (bZ u Tf.til.z0) τ * dOT u o')ᴴ * gramC (gramN D D.R.m le_rfl) (embT D) τ *
      (atInf (embT D) ((((Tf.til.ga c).1)⁻¹ : GL (Fin (D.R.N D.R.m)) D.host.E) : Matrix _ _ D.host.E) τ *
        atInf (embT D) (bZ u Tf.til.z0) τ * dOT u o') = 1 := by
  have e : ∀ (X Y Z G : Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) ℂ),
      (X * Y * Z)ᴴ * G * (X * Y * Z) = Zᴴ * (Yᴴ * (Xᴴ * G * X) * Y) * Z := by
    intro X Y Z G
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [e, ga_inv_unitary, gram_bZ_map, dOT_on _ _ ho]

theorem isUnit_dgE (B' : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E) (hB' : IsUnit B'.det) :
    IsUnit (dgE B').det := by
  unfold dgE
  rw [Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one]
  exact hB'

theorem frame_eq (Tf : FormsTiedSym D u Ch chOf) (c : (D.fm u).clsP) (τ : D.what₂.Tau)
    (B' : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E) (hB' : IsUnit B'.det)
    (o' : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) ℂ) (g : GL (Fin (D.R.N D.R.m - 1)) ℂ)
    (hg : (g : Matrix _ _ ℂ) = (atInf (embT D) B'⁻¹ τ * o')ᵀ) :
    ((gFull D u g : GL (Fin (D.R.N D.R.m)) ℂ) : Matrix _ _ ℂ) =
      ((atInf (embT D) (bZg u Tf.til.z0 B')⁻¹ τ * atInf (embT D) (((Tf.til.ga c).1 : GL (Fin (D.R.N D.R.m)) D.host.E) : Matrix _ _ D.host.E) τ) *
        (atInf (embT D) ((((Tf.til.ga c).1)⁻¹ : GL (Fin (D.R.N D.R.m)) D.host.E) : Matrix _ _ D.host.E) τ *
          atInf (embT D) (bZ u Tf.til.z0) τ * dOT u o'))ᵀ := by
  have hbZ := bZ_isUnitS Tf
  have hd := isUnit_dgE B' hB'
  have h1 := atInf_mul_inv (embT D) ((Tf.til.ga c).1) τ
  have h2 : atInf (embT D) (bZg u Tf.til.z0 B')⁻¹ τ * atInf (embT D) (bZ u Tf.til.z0) τ = ((dgE B')⁻¹).map (embT D τ) := by
    show ((bZg u Tf.til.z0 B')⁻¹).map (embT D τ) * (bZ u Tf.til.z0).map (embT D τ) = _
    rw [bZg_eq_mul, Matrix.mul_inv_rev, Matrix.map_mul, Matrix.mul_assoc, ← Matrix.map_mul, Matrix.nonsing_inv_mul _ hbZ,
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one]
  have h3 : ((dgE B')⁻¹).map (embT D τ) * dOT u o' = ((gFull D u g : GL (Fin (D.R.N D.R.m)) ℂ) : Matrix _ _ ℂ)ᵀ := by
    rw [← dgE_gFull B' hB' o' τ g hg, ← Matrix.mul_assoc, ← Matrix.map_mul, Matrix.nonsing_inv_mul _ hd,
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]
  have e : (atInf (embT D) (bZg u Tf.til.z0 B')⁻¹ τ * atInf (embT D) (((Tf.til.ga c).1 : GL (Fin (D.R.N D.R.m)) D.host.E) : Matrix _ _ D.host.E) τ) *
        (atInf (embT D) ((((Tf.til.ga c).1)⁻¹ : GL (Fin (D.R.N D.R.m)) D.host.E) : Matrix _ _ D.host.E) τ *
          atInf (embT D) (bZ u Tf.til.z0) τ * dOT u o') =
      atInf (embT D) (bZg u Tf.til.z0 B')⁻¹ τ * (atInf (embT D) (((Tf.til.ga c).1 : GL (Fin (D.R.N D.R.m)) D.host.E) : Matrix _ _ D.host.E) τ *
        atInf (embT D) ((((Tf.til.ga c).1)⁻¹ : GL (Fin (D.R.N D.R.m)) D.host.E) : Matrix _ _ D.host.E) τ) *
          atInf (embT D) (bZ u Tf.til.z0) τ * dOT u o' := by
    simp only [Matrix.mul_assoc]
  rw [e, h1, Matrix.mul_one, h2, h3, Matrix.transpose_transpose]

theorem nfAll_smul_reB {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) (a : ℂ) (p : MvPolynomial (ι × Fin n × Fin n) ℂ) :
    (Formalism.L2.Forms.nfAll lam (a • p) (a • p)).re = ‖a‖ ^ 2 * (Formalism.MainNotions.product_first_zeroth_parts.nfAll lam p p).re :=
  Formalism.L2.GlobalTheoryTheory.ColValS.nfAll_smul_self_re lam a p

theorem ipV_co_ofS (Tf : FormsTiedSym D u Ch chOf)
    (B : D.what₂.places.Pl → (D.fm u).clsP → Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E)
    (hB : ∀ w c, IsUnit (B w c).det) (o : FrP D) (ho : ∀ τ, (o.1 τ)ᴴ * gramC (gramP D) (embT D) τ * o.1 τ = 1) :
    ∀ w c, ∀ φ ∈ (D.fm u).Fi D.R.m,
    ((D.fm u).ipV D.R.m ((D.fm u).til c) (φ ((D.fm u).til c)) (φ ((D.fm u).til c))).re =
    (Formalism.MainNotions.product_first_zeroth_parts.nfAll ((D.fm u).lam D.R.m)
      (blk (fun τ => sqAct ℂ _ (lamTr D u τ) (gFull D u (gPof B hB o w c τ))) (coMTS Tf B w c (φ ((D.fm u).til c))))
      (blk (fun τ => sqAct ℂ _ (lamTr D u τ) (gFull D u (gPof B hB o w c τ))) (coMTS Tf B w c (φ ((D.fm u).til c))))).re := by
  classical
  intro w c φ hφ
  obtain ⟨Q, hQ, hq⟩ := trEv_repS Tf (B w c) (hB w c) φ hφ c
  have hcQ : coMTS Tf B w c (φ ((D.fm u).til c)) = Q := by
    simp only [coMTS, LinearMap.coe_comp, Function.comp_apply]
    rw [hq, fnInv_fnOf _ _ _ (atInf_inv_isUnit _ (bZg_isUnitS Tf (B w c) (hB w c)))]
  rw [hcQ]
  set oM1 : D.what₂.Tau → Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) ℂ := fun τ =>
    atInf (embT D) ((((Tf.til.ga c).1)⁻¹ : GL (Fin (D.R.N D.R.m)) D.host.E) : Matrix _ _ D.host.E) τ *
      atInf (embT D) (bZ u Tf.til.z0) τ * dOT u (o.1 τ) with hoM1
  have hon : ∀ τ, (oM1 τ)ᴴ * gramC (gramN D D.R.m le_rfl) (embT D) τ * oM1 τ = 1 := fun τ => frame_on Tf c τ (o.1 τ) (ho τ)
  have hdet : ∀ τ, IsUnit (oM1 τ).det := by
    intro τ
    have h1 := congrArg Matrix.det (hon τ)
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_one] at h1
    have h2 : (oM1 τ).det * ((oM1 τ)ᴴ.det * (gramC (gramN D D.R.m le_rfl) (embT D) τ).det) = 1 := by
      rw [← h1]; ring
    exact ⟨Units.mkOfMulEqOne _ _ h2, rfl⟩
  let oM : Fr D D.R.m le_rfl := ⟨oM1, hdet⟩
  have hoM : oM.IsON := fun τ => Or.inl (hon τ)
  have hg : ∀ τ, ((gFull D u (gPof B hB o w c τ) : GL (Fin (D.R.N D.R.m)) ℂ) : Matrix _ _ ℂ) =
      ((atInf (embT D) (bZg u Tf.til.z0 (B w c))⁻¹ τ *
        atInf (embT D) (((Tf.til.ga c).1 : GL (Fin (D.R.N D.R.m)) D.host.E) : Matrix _ _ D.host.E) τ) * oM.1 τ)ᵀ :=
    fun τ => frame_eq Tf c τ (B w c) (hB w c) (o.1 τ) _ rfl
  set χ : ℂ := (((Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.chi (Tf.tilAd.ka c) : ℂˣ) : ℂ) with hχ
  have hf : φ ((D.fm u).til c) = fun z => fnOf _ (shiftOf (lamT u D.R.m)) (fun τ => (oM.1 τ)⁻¹)
      (χ • blk (fun τ => sqAct ℂ _ (lamTr D u τ) (gFull D u (gPof B hB o w c τ))) Q)
      ((Tf.val D.R.m le_rfl (Or.inr rfl)).eY z) := by
    funext z
    rw [val_of_trEv Tf c _ _ Q hq z, ← map_smul, shift_lamTr,
      fnOf_sqAct _ (lamTr D u) _ (fun τ => oM.1 τ) oM.2 (fun τ => gFull D u (gPof B hB o w c τ)) hg]
  have hmem0 : blk (fun τ => sqAct ℂ _ (lamTr D u τ) (gFull D u (gPof B hB o w c τ))) Q ∈ Formalism.MainNotions.product_first_zeroth_parts.CSpan (lamTr D u) :=
    Formalism.L2.Ker.lc_blk_sqAct_mem _ _ _ (by rw [cspan_lamTr]; exact hQ)
  rw [cspan_lamTr] at hmem0
  have hmem : χ • blk (fun τ => sqAct ℂ _ (lamTr D u τ) (gFull D u (gPof B hB o w c τ))) Q ∈
      Formalism.L2.Forms.CSpan ((D.fm u).lam D.R.m) := Submodule.smul_mem _ _ hmem0
  rw [hf, (Tf.val D.R.m le_rfl (Or.inr rfl)).ipV ((D.fm u).til c) oM hoM _ hmem _ hmem, nfAll_smul_reB,
    hχ, (Tf.glevM).chi_unit (Tf.tilAd.ka c), one_pow, one_mul]

end Main

end Formalism.L2.GlobalTheoryTheory.Br
