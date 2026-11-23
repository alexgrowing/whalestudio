import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.D01CompHolomorphicMap
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarAddVectorScalar
open Matrix Set Filter Topology
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm GlobalTheory.TorsionForm.Pullback
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.d01_comp_holomorphic_eq_d01_fderiv : ∀ {E E' : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E'] [NormedSpace ℂ E'] (φ : E' → E) (H : E → ℂ) (b v : E'), DifferentiableAt ℂ φ b → DifferentiableAt ℝ H (φ b) → d01 (fun c => H (φ c)) b v = d01 H (φ b) (fderiv ℂ φ b v) := by
  first | exact @GlobalTheory.DbarChain.d01_comp_holomorphic | exact GlobalTheory.DbarChain.d01_comp_holomorphic | (intros; apply GlobalTheory.DbarChain.d01_comp_holomorphic <;> assumption)
