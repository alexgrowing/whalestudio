import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleRigidSeparated
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteOrderSt
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AmpleRigid
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ample_rigid_separated : GlobalTheory.AmpleRigid.ConstSt → GlobalTheory.AmpleRigid.CubeSt → GlobalTheory.AmpleRigid.SeparatedSt := by
  first | exact @GlobalTheory.AmpleRigid.separatedSt_of_const_cube | exact GlobalTheory.AmpleRigid.separatedSt_of_const_cube | (intros; apply GlobalTheory.AmpleRigid.separatedSt_of_const_cube <;> assumption)
