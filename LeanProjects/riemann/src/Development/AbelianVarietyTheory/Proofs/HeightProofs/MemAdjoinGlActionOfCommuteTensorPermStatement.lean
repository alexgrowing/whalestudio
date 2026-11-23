import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.MemAdjoinGlActionOfCommuteTensorPerm
import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsLieDataCircle
open GlobalTheory.SmoothForms NumberField Matrix
open scoped ContDiff Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_adjoin_glAction_of_commute_tensorPerm : ∀ (n d : ℕ) (T : Matrix (Fin d → Fin n) (Fin d → Fin n) ℂ), (∀ π, T * permMat n d π = permMat n d π * T) → T ∈ Algebra.adjoin ℂ (Set.range fun p : Fin n × Fin n => polar n d p.1 p.2) := by
  first | exact @GlobalTheory.SymmTensor.mem_adjoin_polar | exact GlobalTheory.SymmTensor.mem_adjoin_polar | (intros; apply GlobalTheory.SymmTensor.mem_adjoin_polar <;> assumption)
