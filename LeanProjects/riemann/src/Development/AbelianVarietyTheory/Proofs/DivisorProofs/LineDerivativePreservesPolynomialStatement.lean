import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineDerivativePreservesPolynomial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CombRSingleNil
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability GlobalTheory.ThK.FiniteLevelDerivatives
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.line_derivative_preserves_polynomial : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), GlobalTheory.ThK.KP → IsTriple B G X om om' →
    ∀ Ψ ∈ GlobalTheory.ThK.PolData B G.M, ∀ γ ∈ Lines σ G.V,
      derL om (fun t => γ (Multiplicative.ofAdd t)) Ψ ∈ GlobalTheory.ThK.PolData B G.M := by
  first | exact @GlobalTheory.ThK.ZFinDerPolL.derL_mem_polData | exact GlobalTheory.ThK.ZFinDerPolL.derL_mem_polData | (intros; apply GlobalTheory.ThK.ZFinDerPolL.derL_mem_polData <;> assumption)
