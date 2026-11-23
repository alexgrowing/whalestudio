import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne

import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem isIntegral_isLocallyNoetherian_compactSpace :
    ∀ (K : Type) [Field K] (A : AbVar K),
      IsIntegral A.X.left ∧ IsLocallyNoetherian A.X.left ∧ CompactSpace A.X.left := by
  intro K _ A
  have hA : IsAbelianScheme A.X := A.ab
  have : Smooth A.X.hom := hA.smooth
  have : IsProper A.X.hom := hA.proper
  have : GeometricallyConnected A.X.hom := hA.geomConnected
  refine ⟨isIntegral_of_smooth_of_geometricallyConnected A.X.hom,
    LocallyOfFiniteType.isLocallyNoetherian A.X.hom, ?_⟩
  exact (quasiCompact_iff_compactSpace A.X.hom).mp inferInstance

end GlobalTheory.AV.AbVar
