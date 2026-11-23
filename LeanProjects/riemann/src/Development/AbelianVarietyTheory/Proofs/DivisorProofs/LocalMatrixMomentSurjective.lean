import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPairOfIsTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerPreservesSchwartzBruhat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharacterNontrivialAtPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplementaryAdelicSchwartzRestFunctionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitPlaceAdelicMatrixGivenComponentsStatement

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LagrCoord

theorem det_ne_zero_of_hasSig {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : HasSig M r s) : M.det ≠ 0 := by
  obtain ⟨hrs, A, hA⟩ := h
  let e : Fin r ⊕ Fin s ≃ Fin n := finSumFinEquiv.trans (finCongr hrs)
  have hD : (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℂ) 0 0 (-1 : Matrix (Fin s) (Fin s) ℂ)).det ≠ 0 := by
    rw [Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, one_mul, Matrix.det_neg, Matrix.det_one, mul_one]
    exact pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
  intro h0
  apply hD
  rw [← hA, ← Matrix.det_submatrix_equiv_self e.symm,
    Matrix.submatrix_mul _ _ e.symm (id : Fin n → Fin n) e.symm Function.bijective_id,
    Matrix.submatrix_mul _ _ e.symm (id : Fin n → Fin n) id Function.bijective_id,
    Matrix.det_mul, Matrix.det_mul, Matrix.submatrix_id_id, h0, mul_zero, zero_mul]

theorem det_ne_zero_of_hasSig_smul {n r s : ℕ} {c : ℂ} {M : Matrix (Fin n) (Fin n) ℂ} (h : HasSig (c • M) r s) :
    M.det ≠ 0 := by
  intro h0
  apply det_ne_zero_of_hasSig h
  rw [Matrix.det_smul, h0, mul_zero]

theorem det_ne_zero_of_map {E : Type} [CommRing E] {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (f : E →+* ℂ)
    (h : (J.map f).det ≠ 0) : J.det ≠ 0 := by
  intro h0
  apply h
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero]

theorem exists_coord : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (n d r s r' s' : ℕ) (X : Spc F E n) (W : Spc F E d), X.IsHerm σ B r s → W.IsSkew σ B r' s' →
    ∀ (v : Pl F) (t : E →ₐ[F] Fv F v) (Y : Matrix (Fin n) (Fin d) (Fv F v)), ∃ x : Matrix (Fin n) (Fin d) (AE F E),
      At (evFin F v) x ∧ x.map (piW t) = 0 ∧ -((1 : GL (Fin n) (Fv F v)).1ᵀ * X.J.map t * (x).map (piW (t.comp σ)) * (W.J.map t)ᵀ * (1 : GL (Fin d) (Fv F v)).1) = Y := by
  intro F E _ _ _ _ _ σ B hB n d r s r' s' X W hX hW v t Y
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have hXd : X.J.det ≠ 0 := det_ne_zero_of_map X.J (B.emb w).1 (det_ne_zero_of_hasSig (hX.sig w))
  have hWd : W.J.det ≠ 0 := det_ne_zero_of_map W.J (B.emb w).1 (det_ne_zero_of_hasSig_smul (hW.sig w))
  have ht : Function.Injective t := t.toRingHom.injective
  have hXt : IsUnit (X.J.map t).det := by
    rw [isUnit_iff_ne_zero]
    intro h0
    apply hXd
    apply ht
    rw [map_zero, ← h0]
    exact (RingHom.map_det t.toRingHom X.J)
  have hWt : IsUnit ((W.J.map t)ᵀ).det := by
    rw [Matrix.det_transpose, isUnit_iff_ne_zero]
    intro h0
    apply hWd
    apply ht
    rw [map_zero, ← h0]
    exact (RingHom.map_det t.toRingHom W.J)
  obtain ⟨x, hxat, hx0, hx1⟩ := GlobalTheory.T.exists_splitPlace_adelicMatrix_given_components hB.cm v t (0 : Matrix (Fin n) (Fin d) (Fv F v))
    (-((X.J.map t)⁻¹ * Y * ((W.J.map t)ᵀ)⁻¹))
  refine ⟨x, hxat, hx0, ?_⟩
  rw [hx1]
  simp only [Units.val_one, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one, Matrix.mul_neg, Matrix.neg_mul, neg_neg]
  rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hWt, Matrix.mul_one,
    Matrix.mul_nonsing_inv_cancel_left _ _ hXt]

end GlobalTheory.LagrCoord
