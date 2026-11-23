import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JointShapeForcedLambda
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.joint_shape_forced_lambda : ∀ (P Q P' Q' R S : ℕ) (κ : ℤ), GlobalTheory.RealLift.Num P Q P' Q' R S κ → (∀ μ' : Formalism.BasicNotions.TH.Ix R S → ℚ, Formalism.BasicNotions.TH.JointShape P Q R S (fun _ => (κ : ℚ) / 2) μ' → μ' = GlobalTheory.RealLift.lam P Q R S κ) ∧ ∀ μ' : Formalism.BasicNotions.TH.Ix R S → ℚ, Formalism.BasicNotions.TH.JointShape P' Q' R S (fun _ => -((κ : ℚ) / 2)) μ' → (fun c => μ' c + (κ : ℚ) / 2) = GlobalTheory.RealLift.lam P Q R S κ := by
  first | exact @GlobalTheory.RealLift.jointShape_halfKappa | exact GlobalTheory.RealLift.jointShape_halfKappa | (intros; apply GlobalTheory.RealLift.jointShape_halfKappa <;> assumption)
