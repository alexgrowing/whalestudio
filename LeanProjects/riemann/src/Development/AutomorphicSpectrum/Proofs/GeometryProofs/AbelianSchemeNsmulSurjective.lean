import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CubeTheorem
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AbelianTorsionFiniteAndMulNSurjective
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PowerMapFlatSemiabelian

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace GlobalTheory.CompanionTheory.Ar.Approx

theorem surjective_pow_of_isAbelianScheme :
    ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∀ n : ℕ, n ≠ 0 →
      Surjective ((𝟙 A) ^ n : A ⟶ A).left := by
  intro K _ A _ hA n hn
  haveI : Smooth A.hom := IsAbelianScheme.smooth (self := hA)
  haveI : IsProper A.hom := IsAbelianScheme.proper (self := hA)
  haveI : GeometricallyConnected A.hom := IsAbelianScheme.geomConnected (self := hA)
  haveI : IsLocallyNoetherian (Sp K) := inferInstanceAs (IsLocallyNoetherian (Spec (CommRingCat.of K)))
  haveI : ConnectedSpace (Sp K) := inferInstanceAs (ConnectedSpace (Spec (CommRingCat.of K)))
  have hw : ((𝟙 A) ^ n : A ⟶ A).left ≫ A.hom = A.hom := Over.w _
  haveI : Flat ((𝟙 A) ^ n : A ⟶ A).left :=
    GlobalTheory.CompanionTheory.Ar.BT.flat_mul_semiAbelian (Sp K) A (GlobalTheory.isSemiAbelian_of_isAbelianScheme A hA) n
      (Nat.one_le_iff_ne_zero.mpr hn)
  haveI : LocallyOfFiniteType ((𝟙 A) ^ n : A ⟶ A).left :=
    HasRingHomProperty.of_comp (fun _ _ h => RingHom.FiniteType.of_comp_finiteType h)
      (by rw [hw]; infer_instance)
  haveI : IsLocallyNoetherian A.left := LocallyOfFiniteType.isLocallyNoetherian A.hom
  haveI : LocallyOfFinitePresentation ((𝟙 A) ^ n : A ⟶ A).left := by
    rw [locallyOfFinitePresentation_iff]
    intro U hU V hV e
    haveI := IsLocallyNoetherian.component_noetherian (X := A.left) ⟨U, hU⟩
    exact RingHom.FinitePresentation.of_finiteType.mp
      (LocallyOfFiniteType.finiteType_of_affine_subset _ hU hV e)
  haveI : UniversallyOpen ((𝟙 A) ^ n : A ⟶ A).left := UniversallyOpen.of_flat _
  haveI : IsProper (((𝟙 A) ^ n : A ⟶ A).left ≫ A.hom) := by rw [hw]; infer_instance
  haveI : IsProper ((𝟙 A) ^ n : A ⟶ A).left := IsProper.of_comp _ A.hom
  haveI : UniversallyOpen A.hom := UniversallyOpen.of_flat _
  haveI : ConnectedSpace A.left := GeometricallyConnected.connectedSpace A.hom A.hom.isOpenMap
  have hclopen : IsClopen (Set.range ((𝟙 A) ^ n : A ⟶ A).left) :=
    ⟨(Scheme.Hom.isClosedMap _).isClosed_range, (Scheme.Hom.isOpenMap _).isOpen_range⟩
  refine ⟨fun y => ?_⟩
  rcases isClopen_iff.mp hclopen with h | h
  · have hy := Set.mem_range_self (f := ⇑((𝟙 A) ^ n : A ⟶ A).left) y
    rw [h] at hy
    exact hy.elim
  · have hy : y ∈ Set.range ⇑((𝟙 A) ^ n : A ⟶ A).left := by rw [h]; trivial
    exact hy

end GlobalTheory.CompanionTheory.Ar.Approx
