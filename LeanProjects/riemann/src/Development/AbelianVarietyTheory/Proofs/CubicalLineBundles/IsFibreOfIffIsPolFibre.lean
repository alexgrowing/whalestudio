import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.LamLetters
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.LamF

theorem isFibreOf_iff_isPolFibre : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Nontrivial R'] (f : R →+* R') (A : Out.PolAV (Sp R)) (x : KeyIn R') (φ : x.P.A.left ⟶ A.A.left), IsFibreOf A x (spMap f) φ ↔ IsPolFibre f A x.P φ := by
  intro R R' _ _ _ f A x φ
  refine ⟨fun h => ⟨?_, h.1, LBIso.symm h.2⟩, fun h => ⟨h.2.1, LBIso.symm h.2.2⟩⟩
  exact H1.dim_unique _ x.P.smoothDim
    ((smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback h.1.1 A.smoothDim)
    (eSec x.P.A (Classical.arbitrary (PrimeSpectrum R')))

end GlobalTheory.LamF
