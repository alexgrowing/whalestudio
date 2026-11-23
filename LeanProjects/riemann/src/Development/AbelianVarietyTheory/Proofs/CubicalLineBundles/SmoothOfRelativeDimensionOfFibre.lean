import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.CM

theorem smoothOfRelativeDimension_of_fibre : ∀ (R K : Type) [CommRing R] [IsDomain R] [Field K] (β : R →+* K) (B : Over (Sp R)) [GrpObj B] (X' : Scheme.{0}) (π : X' ⟶ B.left) (p : X' ⟶ Sp K) (g : ℕ), IsAbelianScheme B → IsPullback π p B.hom (spMap β) → SmoothOfRelativeDimension g p → SmoothOfRelativeDimension g B.hom := by
  intro R K _ _ _ β B _ X' π p g hB hP hg
  have := hB.smooth
  have := hB.geomConnected
  have : ConnectedSpace (Sp R) := inferInstance
  have : ConnectedSpace B.left := GeometricallyConnected.connectedSpace B.hom B.hom.isOpenMap
  obtain ⟨x⟩ : Nonempty B.left := inferInstance
  obtain ⟨n, hn⟩ := exists_dim_of_preconnected B.hom x
  have hn' : SmoothOfRelativeDimension n p :=
    (smoothOfRelativeDimension_isStableUnderBaseChange n).of_isPullback hP hn
  have hs : Surjective B.hom := inferInstance
  have : Surjective p := MorphismProperty.of_isPullback (P := @Surjective) hP hs
  obtain ⟨y, -⟩ := p.surjective (Classical.arbitrary _)
  rw [← H1.dim_unique _ hn' hg y]
  exact hn

end GlobalTheory.CM
