import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocIdeleEqIdl

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.LeviBlockExponent GlobalTheory.CuspBlock GlobalTheory.JacLineSplit
open GlobalTheory.LineFrame

noncomputable section

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LineFrame

section Basis

open Matrix GlobalTheory.SplitGLLift GlobalTheory.KSplit GlobalTheory.JacGeom
open GlobalTheory.Div.CoordOpp (piW_cA incM_map_piW unit_map)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {v : Pl F}
variable {B : Base F E} {d m r s i₀ i₁ : ℕ} {W : Spc F E d} {W₁ : Spc F E m} {H : Plane E d m}

theorem exists_basis_of_unit (hB : B.IsGood σ) (hW : W.IsSkew σ B r s) (hA : H.IsAdapted σ B W W₁ i₀ i₁)
    (e : Fin 1 ⊕ Fin m ⊕ Fin 1 ≃ Fin d) (t : E →ₐ[F] Fv F v) (hJ : IsUnit (W₁.J.map t).det) :
    ∃ hc : IsUnit (((frame H.x H.ι H.y).map t).submatrix id e.symm), ∀ u : GL (Fin d) (Fv F v),
      ∃ h ∈ UAt σ W (evFin F v), locMat t hc.unit h = u ∧
      ∀ N : Matrix _ _ (AE F E), At (evFin F v) (N - 1) → N.map (piW t) = u.val.submatrix e e →
        (u.val.submatrix e e)ᵀ * gram (W₁.J.map t) * N.map (piW (t.comp σ)) = gram (W₁.J.map t) →
        mat h * frame (incV F H.x) (incM F H.ι) (incV F H.y) = frame (incV F H.x) (incM F H.ι) (incV F H.y) * N := by
  have hG := gram_frame_map hB hW hA t
  have hΓ := gram_inv (Matrix.nonsing_inv_mul _ hJ)
  set P := frame H.x H.ι H.y with hP
  generalize fromBlocks _ _ _ _ = Γ' at hΓ
  have hc : IsUnit ((P.map t).submatrix id e.symm) := by
    rw [← Matrix.isUnit_transpose]
    refine IsUnit.of_mul_eq_one ((W.J.map t * P.map (t.comp σ) * Γ').submatrix id e.symm) ?_
    rw [Matrix.transpose_submatrix, ← Matrix.submatrix_mul _ _ _ id _ Function.bijective_id, ← Matrix.mul_assoc,
      ← Matrix.mul_assoc, hG, mul_eq_one_comm.1 hΓ, Matrix.submatrix_one_equiv]
  refine ⟨hc, fun u => ?_⟩
  obtain ⟨h, hh, hu⟩ := GlobalTheory.SkewSplitSurj.exists_locMat_eq F E σ B d W r s hB hW v t hc.unit u
  refine ⟨h, hh, hu, fun N hN h1 h2 => ?_⟩
  have a1 : (mat h).map (piW t) * P.map t = P.map t * u.val.submatrix e e := by
    have b1 : (mat h).map (piW t) * hc.unit.val = hc.unit.val * u.val := by
      rw [← hu, locMat_val, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
    have b2 : P.map t = hc.unit.val.submatrix id e := by simp
    rw [b2, Matrix.submatrix_mul_equiv, ← b1]
    rfl
  have a2 := adj_intertwine e hG hΓ (N₀ := (u⁻¹).val.submatrix e e)
    (by rw [Matrix.submatrix_mul_equiv, Units.mul_inv, Matrix.submatrix_one_equiv]) (unit_map σ h t) a1 h2
  have a3 : frame (incV F H.x) (incM F H.ι) (incV F H.y) = incM F P := by
    ext r (j | j | j) <;> rfl
  rw [a3]
  exact adelic_intertwine hB.cm t hh hN (by rw [h1]; exact a1) a2

end Basis

end GlobalTheory.LineFrame

open GlobalTheory.JacGeom GlobalTheory.SplitGLLift GlobalTheory.KSplit in

theorem GlobalTheory.LineFrame.exists_unip_frameGL : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (d m r s i₀ i₁ : ℕ) (W : Spc F E d) (W₁ : Spc F E m) (H : Plane E d m), B.IsGood σ → W.IsSkew σ B r s →
    ∀ (hA : H.IsAdapted σ B W W₁ i₀ i₁),
      ((GlobalTheory.JacGeom.frame H.x H.ι H.y).submatrix id (GlobalTheory.LineFrame.frameEquiv hA.rank).symm).det ≠ 0 → W₁.J.det ≠ 0 →
      ∀ (v : Pl F) (t : E →ₐ[F] Fv F v) (u : GL (Fin d) (Fv F v)) (X : Matrix (Fin 1) (Fin m ⊕ Fin 1) (Fv F v))
        (Y : Matrix (Fin m) (Fin 1) (Fv F v)),
        (u : Matrix (Fin d) (Fin d) (Fv F v)).submatrix (GlobalTheory.LineFrame.frameEquiv hA.rank) (GlobalTheory.LineFrame.frameEquiv hA.rank) =
          Matrix.fromBlocks 1 X 0 (Matrix.fromBlocks 1 Y 0 1) →
        ∃ g ∈ unip σ W H, g ∈ UAt σ W (evFin F v) ∧
          (mat g).map (piW t) = ((GlobalTheory.LineFrame.frameGL t H hA.rank * u * (GlobalTheory.LineFrame.frameGL t H hA.rank)⁻¹ :
            GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) := by
  intro F E _ _ _ _ _ σ B d m r s i₀ i₁ W W₁ H hB hW hA _ hJ0 v t u X Y hu
  have hJ : IsUnit (W₁.J.map t).det := by
    have : (W₁.J.map t).det = t W₁.J.det := by
      rw [show W₁.J.map t = (t : E →+* Fv F v).mapMatrix W₁.J from rfl, ← RingHom.map_det]; rfl
    rw [this]
    exact isUnit_iff_ne_zero.2 ((map_ne_zero t).2 hJ0)
  obtain ⟨hc, hb⟩ := exists_basis_of_unit hB hW hA (frameEquiv hA.rank) t hJ
  have hcG : frameGL t H hA.rank = hc.unit := Units.ext (frameGL_val t H hA.rank hc)
  obtain ⟨h, hh, h1, h2⟩ := hb u
  obtain ⟨X', Y', hX⟩ := gram_unip (Matrix.mul_nonsing_inv _ hJ) X Y
  refine ⟨h, Subgroup.subset_closure (cols_unip (X := Matrix.of fun i j => liftPair hB.cm t (X i j, X' i j))
    (Y := Matrix.of fun i j => liftPair hB.cm t (Y i j, Y' i j)) (h2 _ (fun a ha => ?_) ?_ ?_)), hh, ?_⟩
  · ext (i | i | i) (j | j | j) <;> simp [Matrix.one_apply, at_liftPair hB.cm t _ a ha]
  · rw [hu]
    ext (i | i | i) (j | j | j) <;> simp [Matrix.one_apply, piW_liftPair, apply_ite (piW t)]
  · rw [hu]
    refine Eq.trans ?_ hX
    congr 1
    ext (i | i | i) (j | j | j) <;> simp [Matrix.one_apply, piW_comp_liftPair, apply_ite (piW (t.comp σ))]
  · rw [hcG, ← h1, Units.val_mul, Units.val_mul, locMat_val]
    simp only [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
    rw [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
