import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.ApartOfNotMem
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.Gal.W2.Seed
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 AfQ Plc sim mat comp rat lev ZU)
open scoped TensorProduct

noncomputable section

namespace UpperTheory.Gal.W2.Seed

variable (R E : Type) [CommRing R] [Algebra ℚ R] [Field E] [NumberField E] (n : ℕ)

private def muHom : R ⊗[ℚ] Matrix (Fin n) (Fin n) E →ₐ[ℚ] Matrix (Fin n) (Fin n) (R ⊗[ℚ] E) :=
  Algebra.TensorProduct.lift
    (((Algebra.ofId (R ⊗[ℚ] E) (Matrix (Fin n) (Fin n) (R ⊗[ℚ] E))).restrictScalars ℚ).comp
      Algebra.TensorProduct.includeLeft)
    (AlgHom.mapMatrix Algebra.TensorProduct.includeRight)
    (fun r x => Algebra.commutes _ _)

private theorem muHom_tmul (r : R) (x : Matrix (Fin n) (Fin n) E) (i k : Fin n) :
    muHom R E n (r ⊗ₜ x) i k = r ⊗ₜ x i k := by
  have h : muHom R E n (r ⊗ₜ x) =
      algebraMap (R ⊗[ℚ] E) (Matrix (Fin n) (Fin n) (R ⊗[ℚ] E)) (r ⊗ₜ 1) *
        x.map (Algebra.TensorProduct.includeRight : E →ₐ[ℚ] R ⊗[ℚ] E) :=
    Algebra.TensorProduct.lift_tmul _ _ _ r x
  rw [h, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, Matrix.smul_apply, Matrix.map_apply]
  simp

private def muInv (M : Matrix (Fin n) (Fin n) (R ⊗[ℚ] E)) : R ⊗[ℚ] Matrix (Fin n) (Fin n) E :=
  ∑ i, ∑ k, LinearMap.lTensor R (Matrix.singleLinearMap ℚ i k) (M i k)

private theorem muInv_add (M N : Matrix (Fin n) (Fin n) (R ⊗[ℚ] E)) :
    muInv R E n (M + N) = muInv R E n M + muInv R E n N := by
  simp [muInv, Matrix.add_apply, map_add, Finset.sum_add_distrib]

private theorem muInv_muHom (y : R ⊗[ℚ] Matrix (Fin n) (Fin n) E) :
    muInv R E n (muHom R E n y) = y := by
  induction y using TensorProduct.induction_on with
  | zero => simp [muInv]
  | add a b ha hb =>
    rw [map_add, muInv_add, ha, hb]
  | tmul r x =>
    simp only [muInv, muHom_tmul, LinearMap.lTensor_tmul, Matrix.singleLinearMap_apply]
    simp only [← TensorProduct.tmul_sum]
    rw [← Matrix.matrix_eq_sum_single x]

private theorem muHom_single (i k : Fin n) (b : R ⊗[ℚ] E) :
    muHom R E n (LinearMap.lTensor R (Matrix.singleLinearMap ℚ i k) b) = Matrix.single i k b := by
  induction b using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb, Matrix.single_add]
  | tmul r x =>
    ext a c
    rw [LinearMap.lTensor_tmul, muHom_tmul, Matrix.singleLinearMap_apply]
    by_cases h : i = a ∧ k = c
    · obtain ⟨rfl, rfl⟩ := h
      simp
    · rw [Matrix.single_apply_of_ne _ _ _ _ _ (by tauto), Matrix.single_apply_of_ne _ _ _ _ _ (by tauto)]
      simp

private theorem muHom_muInv (M : Matrix (Fin n) (Fin n) (R ⊗[ℚ] E)) :
    muHom R E n (muInv R E n M) = M := by
  simp only [muInv, map_sum, muHom_single]
  exact (Matrix.matrix_eq_sum_single M).symm

private def muEquiv : R ⊗[ℚ] Matrix (Fin n) (Fin n) E ≃+* Matrix (Fin n) (Fin n) (R ⊗[ℚ] E) where
  toFun := muHom R E n
  invFun := muInv R E n
  left_inv := muInv_muHom R E n
  right_inv := muHom_muInv R E n
  map_mul' := map_mul _
  map_add' := map_add _

end UpperTheory.Gal.W2.Seed

end

theorem UpperTheory.Gal.W2.Seed.pMuEx :
    MuEx := by
  intro R E _ _ _ _ n
  exact ⟨muEquiv R E n, fun r x i k => muHom_tmul R E n r x i k⟩
