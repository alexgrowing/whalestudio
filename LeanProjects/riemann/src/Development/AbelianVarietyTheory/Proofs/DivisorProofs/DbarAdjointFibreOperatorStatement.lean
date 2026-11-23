import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarAdjointFibreOperator
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarEqZeroOfHolomorphic
open Matrix GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm GlobalTheory.TorsionForm.FlatAcyc
open scoped Real ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dbar_adjoint_fibre_operator : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {g : ℕ}
    (τ : E → Matrix (Fin g) (Fin g) ℂ) (h : Pt E g → ℝ) (b : E) (z : Fin g → ℂ)
    (f : (Fin g → ℂ) → Ext (0 + 0 + g)) (hf : Differentiable ℝ f)
    (hh : DifferentiableAt ℝ h (b, z)) (hpos : 0 < h (b, z)),
    dbarV (fun P : Pt E g => f P.2) (b, z) + dbarAdj τ h (fun P : Pt E g => f P.2) (b, z) =
      fibreOp ((2 : ℂ) • imPart τ b) (fun z' => (Real.log (h (b, z')) : ℂ)) f z := by
  first | exact @GlobalTheory.TorsionForm.FlatAcyc.dbarV_add_dbarAdj_const_eq_fibreOp | exact GlobalTheory.TorsionForm.FlatAcyc.dbarV_add_dbarAdj_const_eq_fibreOp | (intros; apply GlobalTheory.TorsionForm.FlatAcyc.dbarV_add_dbarAdj_const_eq_fibreOp <;> assumption)
