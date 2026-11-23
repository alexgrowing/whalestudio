import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOfRelativeDimensionTensorObjDual
import Mathlib
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.PowObjGeometricallyConnected
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Serre
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smoothOfRelativeDimension_tensorObj_dual_finrank_mul : ∀ (S : Scheme.{0}) (B : Over S) [GrpObj B] [IsCommMonObj B] (O : Type) [CommRing O] [IsDomain O] [Module.Finite ℤ O] (a : OAct O B) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X] (g : ℕ), SmoothOfRelativeDimension g B.hom → SmoothOfRelativeDimension (Module.finrank O X * g) (tensorObj (Module.Dual O X) a).hom := by
  first | exact @GlobalTheory.TensorDualDim.smoothOfRelativeDimension_tensorObj_dual | exact GlobalTheory.TensorDualDim.smoothOfRelativeDimension_tensorObj_dual | (intros; apply GlobalTheory.TensorDualDim.smoothOfRelativeDimension_tensorObj_dual <;> assumption)
