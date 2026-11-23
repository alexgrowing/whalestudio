import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealLineCorrespondsToLine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.real_line_corresponds_to_line : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hσ : ∀ x, σ (σ x) = x), IsCMExt F E σ → ∀ {d : ℕ} (W : Spc F E d) (c : E) (hc : c ≠ 0)
    (γ : ℝ → GAd σ (c • W.J.map σ)), IsRealLine σ (c • W.J.map σ) γ →
    ∃ γL ∈ Lines σ W, ∀ t : ℝ, (toGAd hσ W.J hc).symm (γ t) = γL (Multiplicative.ofAdd t) := by
  first | exact @GlobalTheory.RealLineInU.exists_mem_lines | exact GlobalTheory.RealLineInU.exists_mem_lines | (intros; apply GlobalTheory.RealLineInU.exists_mem_lines <;> assumption)
