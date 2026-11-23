import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LevelMatchIff
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.St

variable {D : D7}

theorem hspace_gram_det_ne {E : Type} [Field E] [NumberField E] [StarRing E] (S : Formalism.BasicNotions.HSpace E) :
    S.gram.det ≠ 0 := by
  intro h
  obtain ⟨v, hv, h0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
  apply hv
  have : S.frame.equivFun.symm v = 0 := by
    refine S.nondeg.2 _ fun x => ?_
    have hx : ∀ i, S.hT (S.frame i) (S.frame.equivFun.symm v) = 0 := fun i => by
      have := congrFun h0 i
      simpa [Matrix.mulVec, dotProduct, Formalism.BasicNotions.HSpace.gram, mul_comm] using this
    rw [← S.frame.sum_repr x]
    simp only [map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, hx, smul_zero,
      Finset.sum_const_zero]
  exact (LinearEquiv.map_eq_zero_iff _).1 this

theorem hform_crd_setting (X : HidaSetting D) (v w : (VS D).V) :
    X.ιE (Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J (X.crd v) (X.crd w)) = (VS D).hT v w := by
  conv_rhs => rw [← X.bas.sum_repr v, ← X.bas.sum_repr w]
  simp only [map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    Formalism.UG.hform, map_mul, HidaSetting.crd, crdOf, starRingEnd_apply, X.ιE_conj, RingEquiv.apply_symm_apply,
    X.J_eq, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [← Formalism.BasicNotions.bridge_star_holds D.R D.host, RingHom.id_apply]
  ring

theorem gram_entry {A : Type} [CommRing A] {n ι : Type} [Fintype n] (σ : A →+* A) (Q : Matrix n ι A)
    (J : Matrix n n A) (k l : ι) :
    ((Q.map σ)ᵀ * J * Q) k l = Formalism.UG.hform σ J (fun i => Q i k) (fun i => Q i l) := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Formalism.UG.hform, Finset.sum_mul]
  exact Finset.sum_comm

def famQ (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V) :
    Fin (D.R.N 0) ⊕ (Fin D.R.rS ⊕ Fin D.R.rS ⊕ Unit) → (VS D).V :=
  Sum.elim (qFr wt) (Sum.elim X.eX (Sum.elim X.fY fun _ => X.zu u))

end GlobalTheory.St

namespace GlobalTheory.St
variable {D : D7}

theorem hT_symm_zero {x y : (VS D).V} (h : (VS D).hT x y = 0) : (VS D).hT y x = 0 := by
  rw [← (VS D).herm.eq x y, h, map_zero]

theorem hT_wt_symm (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hiso : ∀ x y, (VS D).hT (wt x) (wt y) = (VS D).hT x y)
    (x y : (VS D).V) : (VS D).hT (wt.symm x) y = (VS D).hT x (wt y) := by
  rw [← hiso, LinearEquiv.apply_symm_apply]

theorem hT_qFr_qFr (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hiso : ∀ x y, (VS D).hT (wt x) (wt y) = (VS D).hT x y)
    (a b : Fin (D.R.N 0)) : (VS D).hT (qFr wt a) (qFr wt b) = Formalism.L2.Forms.gramN D 0 (Nat.zero_le _) a b := by
  rw [qFr, hT_wt_symm wt hiso, qFr, LinearEquiv.apply_symm_apply, xFr, xFr,
    D.sp.iXY_isom 0 (by have := D.R.two_le_m; omega)]
  rfl

theorem hT_qFr_rest (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hw : WittX X u wt)
    (a : Fin (D.R.N 0)) (k : Fin D.R.rS ⊕ Fin D.R.rS ⊕ Unit) :
    (VS D).hT (qFr wt a) (famQ X u wt (Sum.inr k)) = 0 := by
  obtain ⟨hiso, he, hf, hz⟩ := hw
  rw [qFr, hT_wt_symm wt hiso]
  rcases k with b | b | b
  · simp only [famQ, Sum.elim_inr, Sum.elim_inl, he]; exact (D.sp.hyp_orthX b _).1
  · simp only [famQ, Sum.elim_inr, Sum.elim_inl, hf]; exact (D.sp.hyp_orthX b _).2
  · simp only [famQ, Sum.elim_inr, hz, Formalism.BasicNotions.D7.zmOf, LinearMap.map_smul]
    rw [xFr, D.sp.zm_orth, smul_zero]

end GlobalTheory.St

namespace GlobalTheory.St
variable {D : D7}

theorem hT_fe (X : HidaSetting D) (a b : Fin D.R.rS) :
    (VS D).hT (X.fY a) (X.eX b) = if b = a then 1 else 0 := by
  rw [← (VS D).herm.eq (X.eX b) (X.fY a), X.ef]
  split_ifs <;> simp

theorem hT_ze (X : HidaSetting D) (u : D.what₂.Word) (b : Fin D.R.rS) : (VS D).hT (X.zu u) (X.eX b) = 0 :=
  hT_symm_zero (X.zu_orth u b).1

theorem hT_zf (X : HidaSetting D) (u : D.what₂.Word) (b : Fin D.R.rS) : (VS D).hT (X.zu u) (X.fY b) = 0 :=
  hT_symm_zero (X.zu_orth u b).2

theorem hT_zz_ne (X : HidaSetting D) (u : D.what₂.Word) : (VS D).hT (X.zu u) (X.zu u) ≠ 0 := by
  rw [X.zu_norm, neg_ne_zero, Nat.cast_ne_zero]
  exact ((D.mem u).A.T_prime).ne_zero

def gramR (X : HidaSetting D) (u : D.what₂.Word) :
    Matrix (Fin D.R.rS ⊕ Fin D.R.rS ⊕ Unit) (Fin D.R.rS ⊕ Fin D.R.rS ⊕ Unit) X.B.I.E :=
  Matrix.of fun k l => X.ιE.symm ((VS D).hT (Sum.elim X.eX (Sum.elim X.fY fun _ => X.zu u) k)
    (Sum.elim X.eX (Sum.elim X.fY fun _ => X.zu u) l))

def gramRinv (X : HidaSetting D) (u : D.what₂.Word) :
    Matrix (Fin D.R.rS ⊕ Fin D.R.rS ⊕ Unit) (Fin D.R.rS ⊕ Fin D.R.rS ⊕ Unit) X.B.I.E :=
  Matrix.of fun k l => match k, l with
    | Sum.inl a, Sum.inr (Sum.inl b) => if a = b then 1 else 0
    | Sum.inr (Sum.inl a), Sum.inl b => if a = b then 1 else 0
    | Sum.inr (Sum.inr _), Sum.inr (Sum.inr _) => (X.ιE.symm ((VS D).hT (X.zu u) (X.zu u)))⁻¹
    | _, _ => 0

theorem gramR_mul_inv (X : HidaSetting D) (u : D.what₂.Word) : gramR X u * gramRinv X u = 1 := by
  have ht : X.ιE.symm ((VS D).hT (X.zu u) (X.zu u)) ≠ 0 := by
    rw [Ne, RingEquiv.map_eq_zero_iff]; exact hT_zz_ne X u
  ext (a | a | a) (b | b | b) <;>
    simp [Matrix.mul_apply, Fintype.sum_sum_type, gramR, gramRinv, X.ee, X.ff, X.ef, hT_fe, hT_ze, hT_zf,
      X.zu_orth, Matrix.one_apply, ht, eq_comm]

end GlobalTheory.St

namespace GlobalTheory.St
variable {D : D7}

theorem qFrame_basis_gram : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V), WittX X u wt → ∃ (Q : Matrix (Fin X.B.I.n) (Fin (D.R.N 0) ⊕ (Fin D.R.rS ⊕ Fin D.R.rS ⊕ Unit)) X.B.I.E) (Qi : Matrix (Fin (D.R.N 0) ⊕ (Fin D.R.rS ⊕ Fin D.R.rS ⊕ Unit)) (Fin X.B.I.n) X.B.I.E) (G' : Matrix (Fin D.R.rS ⊕ Fin D.R.rS ⊕ Unit) (Fin D.R.rS ⊕ Fin D.R.rS ⊕ Unit) X.B.I.E), Q * Qi = 1 ∧ Qi * Q = 1 ∧ (∀ j i, Q i (Sum.inl j) = X.crd (qFr wt j) i) ∧ (∀ a i, Q i (Sum.inr (Sum.inl a)) = X.eR a i) ∧ (∀ a i, Q i (Sum.inr (Sum.inr (Sum.inl a))) = X.fR a i) ∧ (∀ i, Q i (Sum.inr (Sum.inr (Sum.inr ()))) = X.zR u i) ∧ IsUnit G'.det ∧ (Q.map (starRingEnd X.B.I.E))ᵀ * X.B.I.J * Q = Matrix.fromBlocks ((Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)).map X.ιE.symm) 0 0 G' := by
  intro D X u wt hw
  classical
  let Q : Matrix (Fin X.B.I.n) (Fin (D.R.N 0) ⊕ (Fin D.R.rS ⊕ Fin D.R.rS ⊕ Unit)) X.B.I.E :=
    Matrix.of fun i k => X.crd (famQ X u wt k) i
  have hiso := hw.1

  have hM : (Q.map (starRingEnd X.B.I.E))ᵀ * X.B.I.J * Q =
      Matrix.fromBlocks ((Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)).map X.ιE.symm) 0 0 (gramR X u) := by
    ext k l
    rw [gram_entry]
    apply X.ιE.injective
    rw [show (fun i => Q i k) = X.crd (famQ X u wt k) from rfl, show (fun i => Q i l) = X.crd (famQ X u wt l) from rfl,
      hform_crd_setting]
    rcases k with a | k <;> rcases l with b | l
    · simp only [Matrix.fromBlocks_apply₁₁, Matrix.map_apply, RingEquiv.apply_symm_apply]
      exact hT_qFr_qFr wt hiso a b
    · simp only [Matrix.fromBlocks_apply₁₂, Matrix.zero_apply, map_zero]
      exact hT_qFr_rest X u wt hw a l
    · simp only [Matrix.fromBlocks_apply₂₁, Matrix.zero_apply, map_zero]
      exact hT_symm_zero (hT_qFr_rest X u wt hw b k)
    · simp only [Matrix.fromBlocks_apply₂₂, gramR, Matrix.of_apply, RingEquiv.apply_symm_apply]
      rfl

  have hA : ((Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)).map X.ιE.symm).det ≠ 0 := by
    have h1 : ((Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)).map X.ιE.symm).det =
        X.ιE.symm.toRingHom (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)).det := by
      rw [RingHom.map_det]; rfl
    rw [h1]
    refine (map_ne_zero _).2 ?_
    unfold Formalism.L2.Forms.gramN
    rw [Matrix.det_reindex_self]
    exact hspace_gram_det_ne _
  have hG : IsUnit (gramR X u).det := Matrix.isUnit_det_of_right_inverse (gramR_mul_inv X u)
  have hMu : IsUnit ((Q.map (starRingEnd X.B.I.E))ᵀ * X.B.I.J * Q).det := by
    rw [hM, Matrix.det_fromBlocks_zero₂₁]
    exact (isUnit_iff_ne_zero.2 hA).mul hG

  have hcard : Fintype.card (Fin (D.R.N 0) ⊕ (Fin D.R.rS ⊕ Fin D.R.rS ⊕ Unit)) = X.B.I.n := by
    rw [X.n_eq, ← dimS_eq, Formalism.BasicNotions.Ranks.N_zero]
    simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_unit]
    omega
  let σ := Fintype.equivFinOfCardEq hcard
  let P := Q.submatrix σ id
  have hQ : Q = P.submatrix σ.symm id := by
    ext i k; simp [P]
  have hconj : (Q.map (starRingEnd X.B.I.E))ᵀ = Qᴴ := by
    ext i k
    simp only [Matrix.conjTranspose_apply, Matrix.transpose_apply, Matrix.map_apply]
    exact starRingEnd_apply _
  have hPJ : (Q.map (starRingEnd X.B.I.E))ᵀ * X.B.I.J * Q = Pᴴ * X.B.I.J.submatrix σ σ * P := by
    have hJ : X.B.I.J = (X.B.I.J.submatrix σ σ).submatrix σ.symm σ.symm := by
      simp [Matrix.submatrix_submatrix]
    rw [hconj, hQ, Matrix.conjTranspose_submatrix]
    conv_lhs => rw [hJ]
    rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, Matrix.submatrix_id_id]
  have hP : IsUnit P.det := by
    rw [hPJ, Matrix.det_mul, Matrix.det_mul] at hMu
    exact isUnit_of_mul_isUnit_right hMu
  refine ⟨Q, (P⁻¹).submatrix id σ.symm, gramR X u, ?_, ?_, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl,
    fun _ => rfl, hG, hM⟩
  · rw [hQ, ← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id, Matrix.mul_nonsing_inv _ hP,
      Matrix.submatrix_one_equiv]
  · rw [hQ, Matrix.submatrix_mul_equiv, Matrix.nonsing_inv_mul _ hP, Matrix.submatrix_id_id]

end GlobalTheory.St
