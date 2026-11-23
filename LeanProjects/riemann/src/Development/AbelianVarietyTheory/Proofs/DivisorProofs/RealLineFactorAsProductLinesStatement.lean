import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealLineFactorAsProductLines
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompFinEqZeroOfAt
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.real_line_factor_as_product_lines : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hσ : ∀ x, σ (σ x) = x), IsCMExt F E σ → ∀ {d : ℕ} (W : Spc F E d) (c : E) (hc : c ≠ 0), ∀ γ ∈ Lines σ W,
    ∃ (k : ℕ) (δ : Fin k → ℝ → GAd σ (c • W.J.map σ)), (∀ i, IsRealLine σ (c • W.J.map σ) (δ i)) ∧
      ∀ t : ℝ, toGAd hσ W.J hc (γ (Multiplicative.ofAdd t)) = (List.ofFn fun i => δ i t).prod := by
  first | exact @GlobalTheory.ThK.LineDec.line_eq_prod_realLines | exact GlobalTheory.ThK.LineDec.line_eq_prod_realLines | (intros; apply GlobalTheory.ThK.LineDec.line_eq_prod_realLines <;> assumption)
