import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealLineMemInfPoints
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.real_line_mem_inf_points : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (β : ℝ → GAd σ J), IsRealLine σ J β → ∀ t, β t ∈ infPts σ J := by
  first | exact @GlobalTheory.RealLineInf.realLine_mem_infPts | exact GlobalTheory.RealLineInf.realLine_mem_infPts | (intros; apply GlobalTheory.RealLineInf.realLine_mem_infPts <;> assumption)
