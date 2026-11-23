import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleRigidConstant
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteOrderSt
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AmpleRigid
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ample_rigid_constant : GlobalTheory.AmpleRigid.ConstSt := by
  first | exact @GlobalTheory.AmpleRigid.constSt | exact GlobalTheory.AmpleRigid.constSt | (intros; apply GlobalTheory.AmpleRigid.constSt <;> assumption)
