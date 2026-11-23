import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsSncPatchRat
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsUnitIffUnitAt

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.SncBase

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase

theorem char_zero_centre_complex_point : ∀ (Ω : Type) [Field Ω] (X : Scheme.{0}) (ξ : Sp Ω ⟶ X)
    (z : Spec (CommRingCat.of ℂ) ⟶ X) (h : genPt ξ ⤳ centre z), IsCptGen ξ → Char0 ξ ⟨centre z, h⟩ := by
  intro Ω _ X ξ z h _
  unfold Char0 InFibre unitAt regAt
  intro r hr hfib
  apply hfib
  have h1 := map_natCast (Scheme.stalkClosedPointTo z).hom r
  have h2 : IsUnit ((r : ℕ) : ℂ) := (Nat.cast_ne_zero.2 hr.ne_zero).isUnit
  rw [← h1] at h2
  obtain ⟨u, hu'⟩ := isUnit_of_map_unit _ _ h2
  have hv : genMap ξ ⟨centre z, h⟩ u.val = (r : Ω) :=
    (congrArg (genMap ξ ⟨centre z, h⟩) hu').trans (map_natCast _ r)
  refine ⟨?_, ⟨_, hv⟩, ⟨(u⁻¹).val, ?_⟩⟩
  · rw [← hv]
    exact (u.isUnit.map (genMap ξ ⟨centre z, h⟩)).ne_zero
  · exact (map_units_inv (genMap ξ ⟨centre z, h⟩) u).trans (congrArg Inv.inv hv)

end GlobalTheory.CompanionTheory.Ar.SncBase
