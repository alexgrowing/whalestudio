import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.D10D01PullbackHolomorphic
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarAddVectorScalar
open Matrix Set Filter Topology
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm GlobalTheory.TorsionForm.Pullback
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.d10_d01_comp_fst_eq_fderiv_of_holomorphic : ∀ {E E' : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E'] [NormedSpace ℂ E'] {g m : ℕ} (φ : E' → E) (F : Pt E g → Ext m) (G : Pt E g → ℂ) (P w : Pt E' g), DifferentiableAt ℂ φ P.1 → DifferentiableAt ℝ F (φ P.1, P.2) → DifferentiableAt ℝ G (φ P.1, P.2) → d10 (fun Q : Pt E' g => F (φ Q.1, Q.2)) P w = d10 F (φ P.1, P.2) (fderiv ℂ φ P.1 w.1, w.2) ∧ d01 (fun Q : Pt E' g => F (φ Q.1, Q.2)) P w = d01 F (φ P.1, P.2) (fderiv ℂ φ P.1 w.1, w.2) ∧ d10 (fun Q : Pt E' g => G (φ Q.1, Q.2)) P w = d10 G (φ P.1, P.2) (fderiv ℂ φ P.1 w.1, w.2) := by
  first | exact @GlobalTheory.TorsionForm.Pullback.d10_d01_comp_fst_eq_fderiv_of_baseChange | exact GlobalTheory.TorsionForm.Pullback.d10_d01_comp_fst_eq_fderiv_of_baseChange | (intros; apply GlobalTheory.TorsionForm.Pullback.d10_d01_comp_fst_eq_fderiv_of_baseChange <;> assumption)
