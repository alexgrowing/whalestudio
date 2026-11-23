import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleRigidSerreAmple
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteOrderSt
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AmpleRigid
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ample_rigid_serre_ample : GlobalTheory.AmpleRigid.FiniteOrderSt → GlobalTheory.AmpleRigid.SeparatedSt → GlobalTheory.AmpleRigid.SerreAmpleSt := by
  first | exact @GlobalTheory.AmpleRigid.serreAmple_of_finiteOrder_of_separated | exact GlobalTheory.AmpleRigid.serreAmple_of_finiteOrder_of_separated | (intros; apply GlobalTheory.AmpleRigid.serreAmple_of_finiteOrder_of_separated <;> assumption)
