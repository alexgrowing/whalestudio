import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechGluingOfKodairaSpencerRelation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenInfOfSeparatedOverAffineOpen
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.TrivPullCompIff
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeTorusCompare
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueIsPullForm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SplitsAt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.AbelianLocusOpenFamilyOverLevel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StructureCohomologyFlatBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianStructureCohomologyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StructureSheafCohomologyPullbackCompCupId
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ConnectedSpaceSpecOfIsLocalRing
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj

set_option autoImplicit false
attribute [local instance] Over.cartesianMonoidalCategory
open TensorProduct

namespace GlobalTheory.AbCohFibre

theorem mem_smul_top_of_tmul_tmul_eq_zero {R S M : Type} [CommRing R] [CommRing S] [Algebra R S] (m : Ideal R)
    [Algebra S (R ⧸ m)] [IsScalarTower R S (R ⧸ m)] [AddCommGroup M] [Module R M] (x : M)
    (hx : ((1 : R ⧸ m) ⊗ₜ[S] ((1 : S) ⊗ₜ[R] x) : (R ⧸ m) ⊗[S] (S ⊗[R] M)) = 0) :
    x ∈ m • (⊤ : Submodule R M) := by
  have h1 := congrArg (AlgebraTensorModule.cancelBaseChange R S (R ⧸ m) (R ⧸ m) M) hx
  rw [AlgebraTensorModule.cancelBaseChange_tmul, one_smul, map_zero] at h1
  have h2 := congrArg (TensorProduct.quotTensorEquivQuotSMul M m) h1
  rw [TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul, map_zero, Submodule.Quotient.mk_eq_zero] at h2
  exact h2

theorem mem_smul_top_of_pull_eq_zero : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ (m : Ideal R), m.IsMaximal → ∀ (Y : Scheme.{0}) (s' : Y ⟶ Sp (R ⧸ m)) (φ : Y ⟶ A.left) (h : IsPullback φ s' A.hom (spMap (algebraMap R (R ⧸ m)))) (x : GlobalTheory.CechDR.HO1 A.hom), GlobalTheory.CechDR.pullHO1 h.w x = 0 → x ∈ m • (⊤ : Submodule R (GlobalTheory.CechDR.HO1 A.hom)) := by
  intro R _ A _ hA m hm Y s' φ h x hx
  haveI : m.IsMaximal := hm
  haveI : m.IsPrime := hm.isPrime
  let f := spMap (algebraMap R (Localization.AtPrime m))
  letI : GrpObj ((Over.pullback f).obj A) := Functor.grpObjObj
  have hAm : IsAbelianScheme ((Over.pullback f).obj A) := GlobalTheory.AbLaw.CubeGen.isAb_baseChange hA f
  obtain ⟨g, hg⟩ := GlobalTheory.AbelianDim.exists_relDim (Localization.AtPrime m) ((Over.pullback f).obj A) hAm
  have hsq0 : IsPullback (pullback.fst A.hom f) ((Over.pullback f).obj A).hom A.hom f :=
    IsPullback.of_hasPullback A.hom f
  have := hA.proper
  obtain ⟨⟨e₁, he₁⟩, -⟩ := GlobalTheory.AbCoh.flat_baseChange_HO R (Localization.AtPrime m) A.left _ A.hom _ _ hsq0
    inferInstance inferInstance
  obtain ⟨-, -, hbc, -⟩ := GlobalTheory.AbCoh.oStr (Localization.AtPrime m) ((Over.pullback f).obj A) g hAm hg
  let ψ : Localization.AtPrime m →+* R ⧸ m :=
    IsLocalization.lift (M := m.primeCompl) (g := Ideal.Quotient.mk m) (fun y : m.primeCompl => by
      show IsUnit (Ideal.Quotient.mk m (y : R))
      have hy : Ideal.Quotient.mk m (y : R) ≠ 0 := by rw [Ne, Ideal.Quotient.eq_zero_iff_mem]; exact y.2
      letI := Ideal.Quotient.field m
      exact isUnit_iff_ne_zero.mpr hy)
  letI : Algebra (Localization.AtPrime m) (R ⧸ m) := ψ.toAlgebra
  have hcomp : (algebraMap (Localization.AtPrime m) (R ⧸ m)).comp (algebraMap R (Localization.AtPrime m)) =
      algebraMap R (R ⧸ m) := IsLocalization.lift_comp _
  haveI : IsScalarTower R (Localization.AtPrime m) (R ⧸ m) := IsScalarTower.of_algebraMap_eq'  hcomp.symm
  have hsp : spMap (algebraMap (Localization.AtPrime m) (R ⧸ m)) ≫ f = spMap (algebraMap R (R ⧸ m)) := by
    show Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hcomp]
  let φ' : Y ⟶ ((Over.pullback f).obj A).left :=
    pullback.lift φ (s' ≫ spMap (algebraMap (Localization.AtPrime m) (R ⧸ m))) (by
      rw [h.w, Category.assoc, hsp])
  have hφ' : φ' ≫ pullback.fst A.hom f = φ := pullback.lift_fst _ _ _
  have hs' : φ' ≫ ((Over.pullback f).obj A).hom = s' ≫ spMap (algebraMap (Localization.AtPrime m) (R ⧸ m)) :=
    pullback.lift_snd _ _ _
  have hbig : IsPullback (φ' ≫ pullback.fst A.hom f) s' A.hom
      (spMap (algebraMap (Localization.AtPrime m) (R ⧸ m)) ≫ f) := by
    rw [hφ', hsp]; exact h
  have hsq : IsPullback φ' s' ((Over.pullback f).obj A).hom (spMap (algebraMap (Localization.AtPrime m) (R ⧸ m))) :=
    IsPullback.of_right hbig hs' hsq0
  obtain ⟨e₂, he₂⟩ := hbc (R ⧸ m) Y s' φ' hsq
  have cong : ∀ (φ₁ : Y ⟶ A.left) (σ₁ : R →+* R ⧸ m) (h₁ : φ₁ ≫ A.hom = s' ≫ spMap σ₁), φ₁ = φ →
      σ₁ = algebraMap R (R ⧸ m) → GlobalTheory.CechDR.pullHO1 h₁ x = GlobalTheory.CechDR.pullHO1 h.w x := by
    rintro _ _ _ rfl rfl; rfl
  have h'' : (φ' ≫ pullback.fst A.hom f) ≫ A.hom =
      s' ≫ spMap ((algebraMap (Localization.AtPrime m) (R ⧸ m)).comp (algebraMap R (Localization.AtPrime m))) := by
    rw [hφ', hcomp]; exact h.w
  have key : GlobalTheory.CechDR.pullHO1 hsq.w (GlobalTheory.CechDR.pullHO1 hsq0.w x) = 0 := by
    rw [GlobalTheory.CechDR.pullHO1_comp hsq0.w hsq.w h'', cong _ _ h'' hφ' hcomp]
    exact hx
  have k1 : ((1 : R ⧸ m) ⊗ₜ[Localization.AtPrime m] (GlobalTheory.CechDR.pullHO1 hsq0.w x)) = 0 := by
    apply e₂.injective
    rw [he₂, map_zero]; exact key
  have k2 := congrArg (LinearMap.lTensor (R ⧸ m) e₁.symm.toLinearMap) k1
  rw [LinearMap.lTensor_tmul, map_zero, ← he₁, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] at k2
  exact mem_smul_top_of_tmul_tmul_eq_zero m x k2

end GlobalTheory.AbCohFibre
