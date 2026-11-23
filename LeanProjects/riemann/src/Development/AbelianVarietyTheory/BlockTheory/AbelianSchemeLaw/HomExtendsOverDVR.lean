import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj

namespace GlobalTheory.IndefiniteRowSideFullHecke.HomExtensionOverDVR

noncomputable abbrev genericPt (T K : Type) [CommRing T] [Field K] [Algebra T K] :
    Spec (.of K) ⟶ Spec (.of T) :=
  Spec.map (CommRingCat.ofHom (algebraMap T K))

def HomExtendsOverDVR : Prop :=
  ∀ (T : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T]
    (K : Type) [Field K] [Algebra T K] [IsFractionRing T K]
    (G G' : Over (Spec (.of T))) [GrpObj G] [GrpObj G'],
    ReciprocityTheory.ChartRestriction.G.Semi.IsSemiAbelian G → ReciprocityTheory.ChartRestriction.G.Semi.IsSemiAbelian G' →
    ∀ f : (Over.pullback (genericPt T K)).obj G ⟶ (Over.pullback (genericPt T K)).obj G',
      IsMonHom f →
      ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (genericPt T K)).map F = f

example (T K : Type) [CommRing T] [Field K] [Algebra T K]
    (G G' : Over (Spec (.of T))) [GrpObj G] [GrpObj G'] (F : G ⟶ G') [IsMonHom F] :
    IsMonHom ((Over.pullback (genericPt T K)).map F) := inferInstance

example (h : HomExtendsOverDVR) (T : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T]
    (G : Over (Spec (.of T))) [GrpObj G] (hG : ReciprocityTheory.ChartRestriction.G.Semi.IsSemiAbelian G)
    (F : G ⟶ G) [IsMonHom F] (hF : (Over.pullback (genericPt T (FractionRing T))).map F = 𝟙 _) :
    F = 𝟙 G := by
  obtain ⟨F₀, -, hu⟩ := h T (FractionRing T) G G hG hG (𝟙 _) inferInstance
  rw [hu F ⟨inferInstance, hF⟩, hu (𝟙 G) ⟨inferInstance, CategoryTheory.Functor.map_id _ _⟩]

end GlobalTheory.IndefiniteRowSideFullHecke.HomExtensionOverDVR
