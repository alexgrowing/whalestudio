import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.ConsAgree
import Development.AbelianVarietyTheory.Definitions.Divisors.ToIThCapDegOfAddNsmulDivP
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ChiLenPicPushforwardOfIsClosedImmersion
open CategoryTheory Limits AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ConsGeo

theorem UpperTheory.functionField_essFiniteType_int :
    ∀ (k : Type) [Field k] [NumberField k] (X : Scheme.{0}) [IsIntegral X] (s : X ⟶ Sp k) [LocallyOfFiniteType s], Algebra.EssFiniteType ℤ X.functionField := by
  intro k _ _ X _ s _
  obtain ⟨x⟩ : Nonempty X := inferInstance
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  haveI : Nonempty U := ⟨⟨x, hxU⟩⟩
  have hU' : IsAffineOpen U := hU
  haveI := functionField_isFractionRing_of_isAffineOpen X U hU'
  have hft : (s.appLE ⊤ U le_top).hom.FiniteType :=
    HasRingHomProperty.appLE @LocallyOfFiniteType s inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU'⟩ le_top
  let φ : k →+* Γ(X, U) := (s.appLE ⊤ U le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom
  have hφ : φ.FiniteType := hft.comp (RingHom.FiniteType.of_surjective _ (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv.surjective)
  letI : Algebra k Γ(X, U) := φ.toAlgebra
  haveI : Algebra.FiniteType k Γ(X, U) := hφ
  haveI h1 : Algebra.EssFiniteType ℤ ℚ := Algebra.EssFiniteType.of_isLocalization ℚ (nonZeroDivisors ℤ)
  haveI h2 : Algebra.EssFiniteType ℤ k := Algebra.EssFiniteType.comp ℤ ℚ k
  haveI h3 : Algebra.EssFiniteType ℤ Γ(X, U) := Algebra.EssFiniteType.comp ℤ k Γ(X, U)
  haveI h4 : Algebra.EssFiniteType Γ(X, U) X.functionField := Algebra.EssFiniteType.of_isLocalization _ (nonZeroDivisors Γ(X, U))
  exact Algebra.EssFiniteType.comp ℤ Γ(X, U) X.functionField
