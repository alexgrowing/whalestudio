import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNontrivialLiftModule
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nontrivial_lift_module : ∀ (P Q R S : ℕ) (x t : ℚ), GlobalTheory.RealLift.HasForm P Q R S x → ∃ (M : Formalism.BasicNotions.TH.GKMod R S) (pr : Formalism.BasicNotions.TH.Pol P Q R S →ₗ[ℂ] M.V), GlobalTheory.RealLift.IsLift x t M pr ∧ Nontrivial M.V := by
  first | exact @GlobalTheory.FockQuot.exists_lift | exact GlobalTheory.FockQuot.exists_lift | (intros; apply GlobalTheory.FockQuot.exists_lift <;> assumption)
