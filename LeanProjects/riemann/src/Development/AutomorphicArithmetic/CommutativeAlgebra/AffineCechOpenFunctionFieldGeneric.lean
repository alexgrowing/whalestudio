import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SortSign
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechModulesFunctorShortExactOfIsAffineOpen
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.OmegaPullOmegaTraceOfSecTraceOne
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.KaehlerOneFormsToExtensionDeRhamMulSelf
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GermSecRestrictGlobalAlgebraMap
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RiemannFormHermitianLattice

open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory GlobalTheory.PD GlobalTheory.CechDR GlobalTheory.HodgeCoh ReciprocityTheory.ChartRestriction.G.Geo.Tor

private theorem smooth_sections_of_affine_open (d : ℕ) (Z : Scheme.{0}) [IsIntegral Z] (p : Z ⟶ Sp ℂ)
    [SmoothOfRelativeDimension d p] (V : Z.Opens) (hV : IsAffineOpen V) :
    Algebra.Smooth ℂ (Sec p V) := by
  have h1 := HasRingHomProperty.appLE @Smooth p (SmoothOfRelativeDimension.smooth d p)
    ⟨⊤, isAffineOpen_top (Sp ℂ)⟩ ⟨V, hV⟩ (by simp)
  have h2 : RingHom.Smooth (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom :=
    RingHom.Smooth.of_bijective (ConcreteCategory.bijective_of_isIso _)
  exact RingHom.Smooth.comp h2 h1

theorem UpperTheory.affineCechOpen_functionField_generic :
    ∀ (d : ℕ) (Z : Scheme.{0}) [IsIntegral Z] (p : Z ⟶ Sp ℂ) [SmoothOfRelativeDimension d p] [inst : Algebra ℂ Z.functionField] (ι : Type) (U : ι → Z.Opens) (B : Finset ι → Subalgebra ℂ Z.functionField) (hinst : inst = ffAlg p) (hU : IsAffCover p U B) (a : ℕ) (s : Finset ι) (hs : s.Nonempty) (hV : IsAffineOpen (cechOpen ⊤ U s)) (hη : genericPoint Z ∈ cechOpen ⊤ U s), letI := algΓ p; Function.Injective (formGermI p a hV hη hinst) ∧ LinearMap.range (formGermI p a hV hη hinst) = omB ℂ Z.functionField (B s) a := by
  intro d Z _ p _ inst ι U B hinst hU a s hs hV hη
  letI := algΓ p
  subst hinst
  letI : Algebra ℂ Z.functionField := ffAlg p
  set V := cechOpen ⊤ U s with hVdef
  letI : Algebra (Sec p V) Z.functionField := (germSec p hη).toAlgebra
  haveI : IsScalarTower ℂ (Sec p V) Z.functionField :=
    IsScalarTower.of_algebraMap_eq (fun r => ((semiHom_germSec p hη).map_algebraMap r).symm)
  haveI : Nonempty V := ⟨⟨_, hη⟩⟩
  haveI : IsFractionRing (Sec p V) Z.functionField :=
    functionField_isFractionRing_of_isAffineOpen Z V hV
  haveI := smooth_sections_of_affine_open d Z p V hV
  have hring : ∀ y, y ∈ B s ↔ ∃ f : Sec p V, algebraMap (Sec p V) Z.functionField f = y := by
    intro y
    rw [hU.ring s hs y]
    have hVeq : s.inf U = V := by
      rw [hVdef]
      simp [cechOpen, Finset.inf_eq_iInf]
    have gen : ∀ (W W' : Z.Opens) (_ : W = W') (h1 : genericPoint Z ∈ W)
        (h2 : genericPoint Z ∈ W'), ((∃ f, (Z.presheaf.germ W _ h1).hom f = y) ↔
          ∃ f, (Z.presheaf.germ W' _ h2).hom f = y) := by
      rintro W W' rfl h1 h2
      rfl
    exact gen _ _ hVeq _ hη
  obtain ⟨hinj, hom⟩ := mOm_injective_and_omB ℂ Z.functionField (Sec p V) (B s) hring a
  have hform : ∀ x, formGermI p a hV hη rfl x =
      ↑((semiHom_algebraMap ℂ (Sec p V) Z.functionField).mOm a
        ((toOmEquiv p a hV).symm ((sectionsOn.toΓ (Omega p a) V) x))) := fun x => rfl
  constructor
  · intro x y hxy
    rw [hform, hform] at hxy
    have h3 := hinj (Subtype.ext hxy)
    exact (sectionsOn.toΓ _ _).injective ((toOmEquiv p a hV).symm.injective h3)
  · ext y
    rw [LinearMap.mem_range, hom y]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨_, (hform x).symm⟩
    · rintro ⟨z, rfl⟩
      refine ⟨(sectionsOn.toΓ (Omega p a) V).symm (toOmEquiv p a hV z), ?_⟩
      rw [hform, AddEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply]
