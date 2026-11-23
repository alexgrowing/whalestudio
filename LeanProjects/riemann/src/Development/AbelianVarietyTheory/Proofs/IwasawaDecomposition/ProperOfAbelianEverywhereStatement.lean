import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ProperOfAbelianEverywhere
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpansAt
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj GlobalTheory.RayEv
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.proper_of_abelian_everywhere : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [CharZero R] (t : SAB H (Sp R)), GlobalTheory.LN.PolAt t (jK R) → abLocus t.G = Set.univ → IsProper t.G.hom := by
  first | exact @GlobalTheory.ProperOfAbelianFibres.isProper_of_polAt_of_abLocus | exact GlobalTheory.ProperOfAbelianFibres.isProper_of_polAt_of_abLocus | (intros; apply GlobalTheory.ProperOfAbelianFibres.isProper_of_polAt_of_abLocus <;> assumption)
