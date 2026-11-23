import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianUnobstructed
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RedHomAlgebraMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCrystallineFormLiftDifferenceEqSum
import Development.AbelianVarietyTheory.Definitions.Divisors.SurjectiveOfIsPullbackSqZero
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.InvFormProj

theorem finite_projective_of_locally_projective (R M : Type) [CommRing R] [AddCommGroup M] [Module R M]
    (h : ∀ q : PrimeSpectrum R, ∃ r : R, r ∉ q.asIdeal ∧ ∃ (F : Type) (_ : AddCommGroup F) (_ : Module R F)
      (_ : Module (Localization.Away r) F) (_ : IsScalarTower R (Localization.Away r) F)
      (_ : Module.Finite (Localization.Away r) F) (_ : Module.Projective (Localization.Away r) F)
      (ϕ : M →ₗ[R] F), IsBaseChange (Localization.Away r) ϕ) :
    Module.Finite R M ∧ Module.Projective R M := by
  let s : Set R := {r | ∃ (F : Type) (_ : AddCommGroup F) (_ : Module R F)
    (_ : Module (Localization.Away r) F) (_ : IsScalarTower R (Localization.Away r) F)
    (_ : Module.Finite (Localization.Away r) F) (_ : Module.Projective (Localization.Away r) F)
    (ϕ : M →ₗ[R] F), IsBaseChange (Localization.Away r) ϕ}
  have hs : Ideal.span s = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hsm⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨r, hr, hP⟩ := h ⟨m, hm.isPrime⟩
    exact hr (hsm (Ideal.subset_span hP))
  have hg : ∀ g : s, g.1 ∈ s := fun g => g.2
  choose F iA iM iL iT iFin iProj ϕ hϕ using hg
  letI := iA
  letI := iM
  letI := iL
  haveI := iT
  haveI := iFin
  haveI := iProj
  haveI (g : s) : IsLocalizedModule (Submonoid.powers g.1) (ϕ g) :=
    (isLocalizedModule_iff_isBaseChange (Submonoid.powers g.1) (Localization.Away g.1) (ϕ g)).2 (hϕ g)
  haveI (g : s) : Module.Flat R (F g) := by
    haveI : Module.Flat R (Localization.Away g.1) :=
      IsLocalization.flat _ (Submonoid.powers g.1)
    exact Module.Flat.trans R (Localization.Away g.1) (F g)
  haveI hfp : Module.FinitePresentation R M :=
    Module.FinitePresentation.of_localizationSpan' s hs (Mₚ := F)
      (Rₚ := fun g : s => Localization.Away g.1) ϕ
      fun _ => Module.finitePresentation_of_projective _ _
  haveI : Module.Flat R M :=
    Module.flat_of_isLocalized_span R M s hs F ϕ fun _ => inferInstance
  exact ⟨inferInstance, Module.Flat.projective_of_finitePresentation⟩

theorem finite_projective : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → (∀ U : AffOp A.left, IsBaseChange (Sec A.hom U.unop.1) (evForm A.hom U ∘ₗ (GlobalTheory.InvForm.InvForm A).subtype)) → Module.Finite R (GlobalTheory.InvForm.InvForm A) ∧ Module.Projective R (GlobalTheory.InvForm.InvForm A) := by
  intro R _ A _ g _ hsm hbc
  haveI : SmoothOfRelativeDimension g A.hom := hsm
  haveI : Smooth A.hom := SmoothOfRelativeDimension.smooth g A.hom
  apply finite_projective_of_locally_projective
  intro q
  let e : Spec (CommRingCat.of R) ⟶ A.left := η[A].left
  have he : e ≫ A.hom = 𝟙 _ := by simp [e]
  obtain ⟨V, hV, hqV, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp A.left.isBasis_affineOpens)
    (show e q ∈ (⊤ : A.left.Opens) from trivial)
  obtain ⟨_, ⟨r, rfl⟩, hr, hsub⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
      (a := q) (u := (e ⁻¹ᵁ V).1) hqV (e ⁻¹ᵁ V).2
  refine ⟨r, hr, ?_⟩
  let y : Sp (Localization.Away r) ⟶ A.left := spMap (algebraMap R (Localization.Away r)) ≫ e
  have hy : ⊤ ≤ y ⁻¹ᵁ V := by
    intro t _
    have : PrimeSpectrum.comap (algebraMap R (Localization.Away r)) t ∈
        (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum R)) := by
      rw [← PrimeSpectrum.localization_away_comap_range (Localization.Away r) r]
      exact ⟨t, rfl⟩
    exact hsub this
  have hs : y ≫ A.hom = spMap (algebraMap R (Localization.Away r)) := by
    simp only [y, Category.assoc, he, Category.comp_id]
  let φ := GlobalTheory.CechKS.FormLocal.valHom (s := A.hom) (U := V) y hy hs
  letI : Algebra (Sec A.hom V) (Localization.Away r) := φ.toRingHom.toAlgebra
  haveI : IsScalarTower R (Sec A.hom V) (Localization.Away r) :=
    IsScalarTower.of_algebraMap_eq fun a => (φ.commutes a).symm
  haveI : Algebra.Smooth R (Sec A.hom V) := smooth_sec_affine A.hom ⟨V, hV⟩
  have hb := hbc (Opposite.op ⟨V, hV⟩)
  exact ⟨Localization.Away r ⊗[Sec A.hom V] Ω[Sec A.hom V⁄R], inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, _,
    hb.comp (TensorProduct.isBaseChange (Sec A.hom V) Ω[Sec A.hom V⁄R] (Localization.Away r))⟩

end GlobalTheory.InvFormProj
