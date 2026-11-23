import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleRigidLevelRigid
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteOrderSt
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AmpleRigid
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ample_rigid_level_rigid : GlobalTheory.AmpleRigid.SerreAmpleSt → GlobalTheory.AmpleRigid.LevelRigidSt := by
  first | exact @GlobalTheory.AmpleRigid.levelRigid_of_serreAmple | exact GlobalTheory.AmpleRigid.levelRigid_of_serreAmple | (intros; apply GlobalTheory.AmpleRigid.levelRigid_of_serreAmple <;> assumption)
