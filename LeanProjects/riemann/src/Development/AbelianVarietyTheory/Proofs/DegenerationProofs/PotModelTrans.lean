import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
namespace GlobalTheory.SS

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in

theorem _root_.GlobalTheory.SS.potModel_trans : ∀ (V K V₁ K₁ : Type) [CommRing V] [Field K] [Algebra V K] [CommRing V₁] [Field K₁] [Algebra V₁ K₁] [Algebra V V₁] [Algebra K K₁], (algebraMap V₁ K₁).comp (algebraMap V V₁) = (algebraMap K K₁).comp (algebraMap V K) → Module.Finite V V₁ → IsLocalHom (algebraMap V V₁) → ∀ (A : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp K)) [GrpObj A] (A₁ : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp K₁)) [GrpObj A₁] (φ : A₁.left ⟶ A.left), _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback A₁ A (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap K K₁)) φ → ∀ Q, _root_.GlobalTheory.SS.PotModel V₁ K₁ A₁ Q → _root_.GlobalTheory.SS.PotModel V K A Q := by
  intro V K V₁ K₁ _ _ _ _ _ _ _ _ hcomm hfin hloc A _ A₁ _ φ hφ Q hP
  obtain ⟨W, L, _, _, _, _, _, _, _, _, h1, h2, h3, h4, G, _, ⟨e, he⟩, hQ⟩ := hP
  letI : Algebra V W := ((algebraMap V₁ W).comp (algebraMap V V₁)).toAlgebra
  letI : Algebra K L := ((algebraMap K₁ L).comp (algebraMap K K₁)).toAlgebra
  have hA : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback ((Over.pullback (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap K₁ L))).obj A₁) A (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap K L)) (pullback.fst A₁.hom (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap K₁ L)) ≫ φ) := by
    refine (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback.comp (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.isGrpPullback_pullback A₁ _) hφ).congr ?_ rfl
    rw [← _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap_comp]
  obtain ⟨e', he', -⟩ := _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.grpPullback_iso hA (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.isGrpPullback_pullback A _)
  refine ⟨W, L, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, ?_, ?_, ?_, h4, G, inferInstance, ⟨e ≪≫ e', ?_⟩, hQ⟩
  · show (algebraMap W L).comp ((algebraMap V₁ W).comp (algebraMap V V₁)) = ((algebraMap K₁ L).comp (algebraMap K K₁)).comp (algebraMap V K)
    rw [← RingHom.comp_assoc, h1, RingHom.comp_assoc, hcomm, RingHom.comp_assoc]
  · exact (RingHom.finite_algebraMap.mpr h2).comp (RingHom.finite_algebraMap.mpr hfin)
  · show IsLocalHom ((algebraMap V₁ W).comp (algebraMap V V₁))
    infer_instance
  · rw [Iso.trans_hom]
    infer_instance

end GlobalTheory.SS
