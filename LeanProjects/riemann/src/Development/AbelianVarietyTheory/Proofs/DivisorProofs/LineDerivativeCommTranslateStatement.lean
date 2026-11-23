import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineDerivativeCommTranslate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.line_derivative_comm_translate : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (f : GAd σ J → ℂ), IsSm σ J f →
    ∀ l : List (ℝ → GAd σ J), (∀ β ∈ l, IsRealLine σ J β) → ∀ γ : ℝ → GAd σ J, IsRealLine σ J γ → ∀ g,
      HasDerivAt (fun t : ℝ => l.foldr lineDer (fun x => f (x * γ t)) g) (l.foldr lineDer (lineDer γ f) g) 0 := by
  first | exact @GlobalTheory.LineDerWord.hasDerivAt_foldr_lineDer_translate | exact GlobalTheory.LineDerWord.hasDerivAt_foldr_lineDer_translate | (intros; apply GlobalTheory.LineDerWord.hasDerivAt_foldr_lineDer_translate <;> assumption)
