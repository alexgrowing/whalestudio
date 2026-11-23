import Mathlib
open CategoryTheory CategoryTheory.Limits TensorProduct

namespace GlobalTheory.QuotientSupportBaseChange

theorem mem_support_baseChange {R A M : Type} [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [Module R M] [Module.Finite R M] (p : PrimeSpectrum A) :
    p ∈ Module.support A (A ⊗[R] M) ↔
      PrimeSpectrum.comap (algebraMap R A) p ∈ Module.support R M := by

  rw [Module.mem_support_iff_nontrivial_residueField_tensorProduct,
    Module.mem_support_iff_nontrivial_residueField_tensorProduct]
  let Kp := p.asIdeal.ResidueField
  let Kq := (PrimeSpectrum.comap (algebraMap R A) p).asIdeal.ResidueField
  have hq : (PrimeSpectrum.comap (algebraMap R A) p).asIdeal = p.asIdeal.comap (algebraMap R A) := rfl
  let _ : Algebra Kq Kp :=
    (Ideal.ResidueField.map (PrimeSpectrum.comap (algebraMap R A) p).asIdeal p.asIdeal (algebraMap R A) hq).toAlgebra
  have : IsScalarTower R Kq Kp := IsScalarTower.of_algebraMap_eq fun r => by
    change algebraMap R Kp r = Ideal.ResidueField.map (PrimeSpectrum.comap (algebraMap R A) p).asIdeal
      p.asIdeal (algebraMap R A) hq (algebraMap R Kq r)
    rw [Ideal.ResidueField.map_algebraMap]
    exact IsScalarTower.algebraMap_apply R A Kp r
  rw [(AlgebraTensorModule.cancelBaseChange R A Kp Kp M).nontrivial_congr,
    ← (AlgebraTensorModule.cancelBaseChange R Kq Kp Kp M).nontrivial_congr]
  exact Module.FaithfullyFlat.nontrivial_tensorProduct_iff_right Kq Kp

theorem nonempty_quotient_equiv {R A M N ι : Type} [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [Module A N]
    [IsScalarTower R A N] (f : M →ₗ[R] N) (hf : IsBaseChange A f) (s : ι → M) :
    Nonempty ((A ⊗[R] (M ⧸ Submodule.span R (Set.range s))) ≃ₗ[A]
      N ⧸ Submodule.span A (Set.range fun i => f (s i))) := by

  let n := Submodule.span R (Set.range s)
  let e₀ := AlgebraTensorModule.tensorQuotientEquiv (R := R) A R A n
  have hmap : (LinearMap.range (AlgebraTensorModule.lTensor A A (n.subtype.restrictScalars R))).map
      (hf.equiv : A ⊗[R] M →ₗ[A] N) = Submodule.span A (Set.range fun i => f (s i)) := by
    change (n.baseChange A).map (hf.equiv : A ⊗[R] M →ₗ[A] N) = _
    rw [Submodule.baseChange_span, Submodule.map_span]
    congr 1
    ext x
    simp [IsBaseChange.equiv_tmul]
  exact ⟨e₀.trans (Submodule.Quotient.equiv _ _ hf.equiv hmap)⟩

theorem mem_support_quotient_iff (R S R' S' : CommRingCat.{0}) (qa : R ⟶ S) (ba : R ⟶ R')
    (ga : S ⟶ S') (qa' : R' ⟶ S') (h : IsPushout qa ba ga qa') (hfin : qa.hom.Finite)
    {ι : Type} (s : ι → S) (p : PrimeSpectrum R') :
    ((letI := qa'.hom.toAlgebra; p ∈ Module.support R'
        (S' ⧸ Submodule.span R' (Set.range (fun i => ga.hom (s i))))) ↔
      (letI := qa.hom.toAlgebra; PrimeSpectrum.comap ba.hom p ∈ Module.support R
        (S ⧸ Submodule.span R (Set.range s)))) := by
  let _ : Algebra R R' := ba.hom.toAlgebra
  let _ : Algebra R S := qa.hom.toAlgebra
  let _ : Algebra R' S' := qa'.hom.toAlgebra
  let _ : Algebra S S' := ga.hom.toAlgebra
  let _ : Algebra R S' := (qa ≫ ga).hom.toAlgebra
  have : IsScalarTower R R' S' := IsScalarTower.of_algebraMap_eq fun r => by
    change (qa ≫ ga).hom r = qa'.hom (ba.hom r)
    rw [h.w]
    rfl
  have : IsScalarTower R S S' := IsScalarTower.of_algebraMap_eq fun r => rfl
  have hpo : Algebra.IsPushout R R' S S' := CommRingCat.isPushout_iff_isPushout.mp h.flip
  have : Module.Finite R S := hfin

  obtain ⟨e⟩ : Nonempty ((R' ⊗[R] (S ⧸ Submodule.span R (Set.range s))) ≃ₗ[R']
      S' ⧸ Submodule.span R' (Set.range fun i => ga.hom (s i))) :=
    nonempty_quotient_equiv _ hpo.out s
  have key : p ∈ Module.support R' (S' ⧸ Submodule.span R' (Set.range fun i => ga.hom (s i))) ↔
      PrimeSpectrum.comap ba.hom p ∈ Module.support R (S ⧸ Submodule.span R (Set.range s)) := by
    rw [← e.support_eq]
    exact mem_support_baseChange p
  exact key

end GlobalTheory.QuotientSupportBaseChange
