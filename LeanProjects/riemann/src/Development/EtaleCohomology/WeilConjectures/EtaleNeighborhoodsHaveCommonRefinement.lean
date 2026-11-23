import Development.EtaleCohomology.WeilConjectures.AbsorbPf

noncomputable section
open CategoryTheory LateralTheory.E.t_E3Cut TensorProduct

namespace LateralTheory.EWeil.AbsorbPf2

theorem etaleNeighborhoods_have_common_refinement : LateralTheory.EWeil.AbsorbPf.Pair := by
  intro A B C Ω _ ι gB gC hB hC φB φC hφB hφC
  letI := gB.hom.toAlgebra
  letI := gC.hom.toAlgebra
  letI := ι.toAlgebra
  haveI : Algebra.Etale A B := (RingHom.etale_algebraMap (R := A) (S := B)).mp hB
  haveI : Algebra.Etale A C := (RingHom.etale_algebraMap (R := A) (S := C)).mp hC
  let φB' : B →ₐ[A] Ω := { φB with commutes' := fun a => RingHom.congr_fun hφB a }
  let φC' : C →ₐ[A] Ω := { φC with commutes' := fun a => RingHom.congr_fun hφC a }
  let L := Algebra.TensorProduct.lift φB' φC' (fun _ _ => Commute.all _ _)
  refine ⟨CommRingCat.of (B ⊗[A] C), CommRingCat.ofHom (algebraMap A (B ⊗[A] C)), L.toRingHom,
    CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom,
    CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := A) (A := B) (B := C)).toRingHom,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · haveI : Algebra.Etale B (B ⊗[A] C) := inferInstance
    haveI : Algebra.Etale A (B ⊗[A] C) := Algebra.Etale.comp A B (B ⊗[A] C)
    exact (RingHom.etale_algebraMap (R := A) (S := B ⊗[A] C)).mpr inferInstance
  · ext a; exact L.commutes a
  · ext a
    show (gB.hom a) ⊗ₜ[A] (1 : C) = algebraMap A (B ⊗[A] C) a
    rw [Algebra.TensorProduct.algebraMap_apply]; rfl
  · ext a
    show (1 : B) ⊗ₜ[A] (gC.hom a) = algebraMap A (B ⊗[A] C) a
    rw [Algebra.TensorProduct.algebraMap_apply]
    exact (Algebra.TensorProduct.tmul_one_eq_one_tmul (R := A) (A := B) (B := C) a).symm
  · ext b
    show L (b ⊗ₜ 1) = φB b
    simp [L, φB']
  · ext c
    show L (1 ⊗ₜ c) = φC c
    simp [L, φC']

end LateralTheory.EWeil.AbsorbPf2
