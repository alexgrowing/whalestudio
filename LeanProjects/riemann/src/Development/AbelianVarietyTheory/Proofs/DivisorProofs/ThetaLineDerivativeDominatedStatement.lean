import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLineDerivativeDominated
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CombRSingleNil
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability GlobalTheory.ThK.FiniteLevelDerivatives
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_along_line_le_integrableOn_bound : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), GlobalTheory.ThK.KP → IsTriple B G X om om' →
    ∀ Ψ ∈ GlobalTheory.ThK.PolData B G.M, ∀ γ ∈ Lines σ G.V, ∀ h, ∃ b : UA σ G.V.J → ℝ, IntegrableOn b G.M.dom G.M.μ ∧
      ∀ g ∈ G.M.dom, ∀ t ∈ Set.Ioo (-1 : ℝ) 1, ‖theta om Ψ (g * γ (Multiplicative.ofAdd t)) h‖ ≤ b g := by
  first | exact @GlobalTheory.ThK.ZFinDom.dom | exact GlobalTheory.ThK.ZFinDom.dom | (intros; apply GlobalTheory.ThK.ZFinDom.dom <;> assumption)
