import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AbelianPartIsoCarriesSymmetryValues
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIsFib
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
open GlobalTheory.Ex.AbPartIso
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianPartIso_carries_symmetry_values : GlobalFnsSt → AllIso fun {_} _ _ {_} {_} {F} _ _ {N} {N'} ν ν' {_} w f => ∀ x, (N'.σ (f x) : F) * wVal ν ν' w f x = (N.σ x : F) * wVal ν ν' w f x⁻¹ := by
  first | exact @GlobalTheory.AbPartSym.sym_values | exact GlobalTheory.AbPartSym.sym_values | (intros; apply GlobalTheory.AbPartSym.sym_values <;> assumption)
