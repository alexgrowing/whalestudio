import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleRigidFiniteOrder
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteOrderSt
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AmpleRigid
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ample_rigid_finite_order : GlobalTheory.AmpleRigid.ConstSt → GlobalTheory.AmpleRigid.CubeSt → GlobalTheory.AmpleRigid.FiniteOrderSt := by
  first | exact @GlobalTheory.AmpleFiniteOrder.finiteOrder_of_const_of_cube | exact GlobalTheory.AmpleFiniteOrder.finiteOrder_of_const_of_cube | (intros; apply GlobalTheory.AmpleFiniteOrder.finiteOrder_of_const_of_cube <;> assumption)
