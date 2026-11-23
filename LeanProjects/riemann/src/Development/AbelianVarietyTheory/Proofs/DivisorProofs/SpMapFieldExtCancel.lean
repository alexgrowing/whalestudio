import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem spMap_field_cancel (Ω Ω' : Type) [Field Ω] [Field Ω'] (io : Ω →+* Ω') (X : Scheme.{0}) (a b : Sp Ω ⟶ X)
    (h : spMap io ≫ a = spMap io ≫ b) : a = b := by
  haveI : Epi (spMap io) := Flat.epi_of_flat_of_surjective _
  exact (cancel_epi (spMap io)).1 h

end GlobalTheory.Mum
