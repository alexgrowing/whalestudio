import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraicPointLiftsAlongFinite
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCochFrame
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open AlgebraicGeometry CategoryTheory Limits NumberField MonoidalCategory CartesianMonoidalCategory MonObj Matrix Topology
open Formalism.BasicNotions ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CubeFib GlobalTheory.LieMet GlobalTheory.LieHt GlobalTheory.LocM.Frm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh GlobalTheory.Toroidal GlobalTheory.HeightParts GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.BdFib
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algebraic_point_lifts_along_finite : ∀ (W Y : Scheme.{0}) [IsIntegral W] (π : W ⟶ Y), IsFinite π → ∀ y : Sp Qb ⟶ Y, π (genericPoint W) ⤳ y (IsLocalRing.closedPoint Qb) → ∃ w : Sp Qb ⟶ W, w ≫ π = y := by
  first | exact @GlobalTheory.CovLift.exists_lift_of_specializes | exact GlobalTheory.CovLift.exists_lift_of_specializes | (intros; apply GlobalTheory.CovLift.exists_lift_of_specializes <;> assumption)
