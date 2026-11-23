import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV

theorem exists_smoothOfRelativeDimension_of_isAbelianScheme :
    ∀ (K : Type) [Field K] (X : Over (Sp K)) [GrpObj X], IsAbelianScheme X →
      ∃ g : ℕ, SmoothOfRelativeDimension g X.hom := by
  intro K _ X _ hX
  haveI := hX.smooth
  haveI := hX.geomConnected
  haveI : ConnectedSpace X.left := GeometricallyConnected.connectedSpace X.hom X.hom.isOpenMap
  obtain ⟨x₀⟩ := (inferInstance : ConnectedSpace X.left).toNonempty
  exact exists_dim_of_preconnected X.hom x₀

end GlobalTheory.AV
