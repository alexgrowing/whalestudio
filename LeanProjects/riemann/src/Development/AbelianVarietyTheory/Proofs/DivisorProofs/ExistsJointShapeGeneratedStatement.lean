import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsJointShapeGenerated
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_joint_shape_generated : ∀ (P Q R S : ℕ) (x t : ℚ) (M : Formalism.BasicNotions.TH.GKMod R S) (pr : Formalism.BasicNotions.TH.Pol P Q R S →ₗ[ℂ] M.V), GlobalTheory.RealLift.IsLift x t M pr → Nontrivial M.V → ∃ μ' : Formalism.BasicNotions.TH.Ix R S → ℚ, Formalism.BasicNotions.TH.JointShape P Q R S (fun _ => x) μ' ∧ GlobalTheory.RealLift.GenBy M (fun c => μ' c + t) := by
  first | exact @GlobalTheory.RealLift.GenLift.genBy_of_isLift | exact GlobalTheory.RealLift.GenLift.genBy_of_isLift | (intros; apply GlobalTheory.RealLift.GenLift.genBy_of_isLift <;> assumption)
