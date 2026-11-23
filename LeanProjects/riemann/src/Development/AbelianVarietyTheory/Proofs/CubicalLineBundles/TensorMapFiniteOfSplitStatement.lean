import Mathlib
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.TensorMapFiniteOfSplit
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.PowObjGeometricallyConnected
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Serre
open scoped CategoryTheory.Obj UpperHalfPlane TensorProduct
theorem _root_.GlobalTheory.T.tensor_map_finite_of_split : Out.Laws → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : Out.PolAV S) [IsCommMonObj P.A] (O : Type) [CommRing O] (M : Type) [AddCommGroup M] [Module O M] [Module.Finite O M] [Module.Projective O M] (A : Over S) [GrpObj A] [IsCommMonObj A] (a : OAct O P.A) (b : OAct O A) (t : IsTensor A b P.A a M) (n k : ℕ) (l : M →ₗ[O] (Fin k → O)) (r : (Fin k → O) →ₗ[O] M), 0 < n → (∀ m, r (l m) = n • m) → IsFinite (t.mapLeft (IsTensor.pow (Out.powIsPowGrp P.A k) a) l).left := by
  first | exact @GlobalTheory.TensorFinite.isFinite_mapLeft | exact GlobalTheory.TensorFinite.isFinite_mapLeft | (intros; apply GlobalTheory.TensorFinite.isFinite_mapLeft <;> assumption)
