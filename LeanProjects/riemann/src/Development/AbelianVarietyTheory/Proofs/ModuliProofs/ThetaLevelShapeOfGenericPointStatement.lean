import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaLevelShapeOfGenericPoint
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLevelShape_of_generic_point : Out.Laws → Out.Laws2 → ∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) Mat κ (S : Scheme.{0}) [IsLocallyNoetherian S] [IsIntegral S] (s : S ⟶ Sp o) (t : TObj g k J b s) (K : Type) [Field K] (x : Sp K ⟶ S) (s' : Sp K ⟶ Sp o) (tK : TObj g k J b s'), Set.range x = {genericPoint S} → TMap tK t x → tK.Shape Mat κ → t.Shape Mat κ := by
  first | exact @GlobalTheory.shape_of_generic | exact GlobalTheory.shape_of_generic | (intros; apply GlobalTheory.shape_of_generic <;> assumption)
