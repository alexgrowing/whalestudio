import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsKilledByOperatorProductsSuccCreationApply
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.StarPurelyImaginaryEqNeg
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isKilledByOperatorProducts_succ_creation_apply : ∀ (I M : Type) [AddCommGroup M] [Module ℂ M] (a : I → Module.End ℂ M) (c : Module.End ℂ M), (∀ i, ∃ β : ℂ, a i * c - c * a i = β • (1 : Module.End ℂ M)) → ∀ (N : ℕ) (m : M), Killed a N m → Killed a (N + 1) (c m) := by
  first | exact @GlobalTheory.FockCompare.WeylCreate.killed_create | exact GlobalTheory.FockCompare.WeylCreate.killed_create | (intros; apply GlobalTheory.FockCompare.WeylCreate.killed_create <;> assumption)
