import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiAdjTensorPowerIntMatrixEndomorphism
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMonHomOfMulComp
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rosatiAdj_tensorPowerIntMatrixEndomorphism : ∀ (R : Type) [CommRing R] [IsDomain R] (D D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D D' W) (A A' : Matrix (Fin r) (Fin r) ℤ), A.transpose * (W + W.transpose) = (W + W.transpose) * A' → RosatiAdj D'.P.A D'.P.L (GlobalTheory.TensAct.matAct T A) (GlobalTheory.TensAct.matAct T A') := by
  first | exact @GlobalTheory.TensAct.rosatiAdj_matAct | exact GlobalTheory.TensAct.rosatiAdj_matAct | (intros; apply GlobalTheory.TensAct.rosatiAdj_matAct <;> assumption)
