import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenFarSet
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.SemiAbFibre

theorem irreducibleSpace_fibre : ∀ (T : Scheme.{0}) (G : Over T) [GrpObj G], IsSemiAbelian G → ∀ (Ω : Type) [Field Ω] (x : Sp Ω ⟶ T), IrreducibleSpace (pullback G.hom x : Scheme.{0}) := by
  intro T G _ hG Ω _ x
  have := hG.smooth
  have := hG.geomConnected
  have h : GeometricallyIntegral G.hom := GlobalTheory.geometricallyIntegral_of_smooth _
  have : IsIntegral (pullback G.hom x : Scheme.{0}) :=
    h.geometrically_isIntegral _ _ _ (IsPullback.of_hasPullback G.hom x)
  infer_instance

end GlobalTheory.SemiAbFibre
