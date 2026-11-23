import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineToGAdDerivative
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.line_to_GAd_derivative : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hσ : ∀ x, σ (σ x) = x), IsCMExt F E σ → ∀ (d : ℕ) (W : Spc F E d) (c : E) (hc : c ≠ 0),
    ∀ γ ∈ Lines σ W, ∃ (r : ℕ) (β : Fin r → ℝ → GAd σ (c • W.J.map σ)), (∀ i, IsRealLine σ (c • W.J.map σ) (β i)) ∧
      ∀ f, IsSm σ (c • W.J.map σ) f → ∀ g,
        HasDerivAt (fun t : ℝ => f (g * toGAd hσ W.J hc (γ (Multiplicative.ofAdd t)))) (∑ i, lineDer (β i) f g) 0 := by
  first | exact @GlobalTheory.LineDerSum.exists_lines_hasDerivAt | exact GlobalTheory.LineDerSum.exists_lines_hasDerivAt | (intros; apply GlobalTheory.LineDerSum.exists_lines_hasDerivAt <;> assumption)
