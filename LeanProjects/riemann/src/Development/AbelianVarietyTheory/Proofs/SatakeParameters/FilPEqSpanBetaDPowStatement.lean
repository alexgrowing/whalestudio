import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FilPEqSpanBetaDPow
import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LMulBeta
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Polynomial GlobalTheory.Pst GlobalTheory.MemLoc GlobalTheory.Pst.StLat GlobalTheory.Pst.NoLog
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.filP_eq_span_betaD_pow_of_kerP_eq_span_beta : ∀ (l : ℕ) [Fact l.Prime] (Co : Core l) (ϖ : Per.Fl l), Per.kerP l = Ideal.span {beta ϖ} →
  ∀ n : ℕ, Per.FilP l n = Ideal.span {betaD ϖ ^ n} := by
  first | exact @GlobalTheory.Pst.StLat.filtration_eq_span_pow | exact GlobalTheory.Pst.StLat.filtration_eq_span_pow | (intros; apply GlobalTheory.Pst.StLat.filtration_eq_span_pow <;> assumption)
