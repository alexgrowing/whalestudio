import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExpandsPullOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdFam
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TWMain
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadraticAlgebraValuation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SmoothIsMultiplicative

namespace GlobalTheory.PowGrp

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

theorem quasiCompact_geomConnected_pow : ∀ (S : Scheme.{0}) (G' G : Over S) [GrpObj G'] [GrpObj G] (j : ℕ) (p : IsPowGrp G' G j), (QuasiCompact G.hom → QuasiCompact G'.hom) ∧ (Smooth G.hom → GeometricallyConnected G.hom → GeometricallyConnected G'.hom) := by
  intro S G' G _ _ j p
  refine ⟨prop_of_isPowGrp @QuasiCompact p, fun hs hc => ?_⟩
  obtain ⟨e, he, hw⟩ := exists_iso_powObj p
  have := geomConnected_powObj G j
  have := smooth_isMultiplicative
  have : Smooth (powObj G j).hom := prop_powObj @Smooth G hs j
  have := geomConnected_of_isIso e
  rw [hw]
  exact GeometricallyConnected.comp _ _

end GlobalTheory.PowGrp
