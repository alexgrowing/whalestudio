import Development.EtaleCohomology.EtaleSheaves.LeafRoofEtPPf

noncomputable section
open TensorProduct

namespace LateralTheory.E.LeafPolyEtPf

theorem LeafPolyEt_of : LateralTheory.E.LeafRoofEtPPf.LeafPolyEt := by
  intro d C B D _ _ _ _ φ hφ
  letI : Algebra C B := (φ.comp MvPolynomial.C).toAlgebra
  let P := MvPolynomial (Fin d) C
  letI : Algebra P B := φ.toAlgebra
  haveI : IsScalarTower C P B := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : Algebra.Etale P B := by rw [← RingHom.etale_algebraMap]; exact hφ
  let e2 : MvPolynomial (Fin d) D ≃+* P ⊗[C] D :=
    (MvPolynomial.algebraTensorAlgEquiv (σ := Fin d) C D).symm.toRingEquiv.trans (Algebra.TensorProduct.comm C D P).toRingEquiv
  let e1 : (P ⊗[C] D) ⊗[P] B ≃ₐ[P] B ⊗[C] D :=
    (Algebra.TensorProduct.comm P (P ⊗[C] D) B).trans (Algebra.TensorProduct.cancelBaseChange C P P B D)
  have hg : (algebraMap (P ⊗[C] D) ((P ⊗[C] D) ⊗[P] B)).Etale :=
    RingHom.etale_algebraMap.mpr inferInstance
  have key : MvPolynomial.eval₂Hom (Algebra.TensorProduct.includeRight : D →ₐ[C] B ⊗[C] D).toRingHom
      (fun j => φ (MvPolynomial.X j) ⊗ₜ[C] (1:D)) =
      (e1.toRingEquiv.toRingHom.comp (algebraMap (P ⊗[C] D) ((P ⊗[C] D) ⊗[P] B))).comp
        e2.toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp only [e1, e2, RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
        RingEquiv.coe_trans, AlgEquiv.coe_ringEquiv]
      rw [show (MvPolynomial.C r : MvPolynomial (Fin d) D) = MvPolynomial.monomial 0 r from rfl,
        MvPolynomial.algebraTensorAlgEquiv_symm_monomial]
      simp only [MvPolynomial.monomial_zero', MvPolynomial.C_1]
      show _ = (Algebra.TensorProduct.cancelBaseChange C P P B D)
        ((Algebra.TensorProduct.comm P (P ⊗[C] D) B) (((1 : P) ⊗ₜ[C] r) ⊗ₜ[P] (1 : B)))
      simp
    · intro j
      simp [e1, e2]
      rw [Algebra.smul_def, mul_one]; rfl
  rw [key]
  have hc := RingHom.Etale.stableUnderComposition
  exact hc _ _ (RingHom.Etale.of_bijective e2.bijective) (hc _ _ hg (RingHom.Etale.of_bijective e1.bijective))

end LateralTheory.E.LeafPolyEtPf
