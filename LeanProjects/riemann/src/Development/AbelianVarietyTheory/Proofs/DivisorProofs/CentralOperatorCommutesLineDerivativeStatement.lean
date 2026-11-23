import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentralOperatorCommutesLineDerivative
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompFinEqZeroOfAt
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.central_operator_commutes_line_derivative : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (z : List (ℝ → GAd σ J) →₀ ℂ), IsCentral σ J z →
    ∀ f : GAd σ J → ℂ, IsSm σ J f → ∀ γ : ℝ → GAd σ J, IsRealLine σ J γ → lineDer γ (dop z f) = dop z (lineDer γ f) := by
  first | exact @GlobalTheory.UAut.CentralComm.lineDer_dop_comm | exact GlobalTheory.UAut.CentralComm.lineDer_dop_comm | (intros; apply GlobalTheory.UAut.CentralComm.lineDer_dop_comm <;> assumption)
