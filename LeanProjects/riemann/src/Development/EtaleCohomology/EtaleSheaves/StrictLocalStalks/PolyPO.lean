import Development.EtaleCohomology.EtaleSheaves.StrictLocalStalks

open CategoryTheory Limits LateralTheory.E.t_E3Cut

namespace LateralTheory.E.ULAStalkPf

theorem polyPO : PolyPO := by
  intro A B b
  let _ : Algebra A B := b.hom.toAlgebra
  let _ : Algebra (Polynomial A) (Polynomial B) := (Polynomial.mapRingHom b.hom).toAlgebra
  have _ : IsScalarTower A (Polynomial A) (Polynomial B) := IsScalarTower.of_algebraMap_eq (fun a => by
    change Polynomial.C (b.hom a) = Polynomial.map b.hom (Polynomial.C a)
    rw [Polynomial.map_C])
  have hP : Algebra.IsPushout A B (Polynomial A) (Polynomial B) := by
    refine ⟨IsBaseChange.of_equiv (polyEquivTensor' A B).symm.toLinearEquiv (fun p => ?_)⟩
    change (polyEquivTensor A B).symm (1 ⊗ₜ p) = Polynomial.map b.hom p
    rw [polyEquivTensor_symm_apply_tmul_eq_smul, one_smul]; rfl
  exact CommRingCat.isPushout_iff_isPushout.mpr hP.symm

end LateralTheory.E.ULAStalkPf
