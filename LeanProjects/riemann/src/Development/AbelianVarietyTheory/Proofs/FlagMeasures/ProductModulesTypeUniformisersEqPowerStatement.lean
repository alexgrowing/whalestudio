import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ProductModulesTypeUniformisersEqPower
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGHTie
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.product_modules_type_uniformisers_eq_power : Formalism.L2.SG.NGHTie.HTTheta := by
  first | exact @GlobalTheory.HTThetaLeaf.main | exact GlobalTheory.HTThetaLeaf.main | (intros; apply GlobalTheory.HTThetaLeaf.main <;> assumption)
