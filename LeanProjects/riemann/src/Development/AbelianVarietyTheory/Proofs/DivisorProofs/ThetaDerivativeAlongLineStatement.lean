import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaDerivativeAlongLine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CombRSingleNil
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability GlobalTheory.ThK.FiniteLevelDerivatives
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_derivative_along_line : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), GlobalTheory.ThK.KP → IsTriple B G X om om' →
    ∀ Ψ ∈ GlobalTheory.ThK.PolData B G.M, ∀ γ ∈ Lines σ G.V, ∀ g h,
      HasDerivAt (fun t : ℝ => theta om Ψ (g * γ (Multiplicative.ofAdd t)) h)
        (theta om (derL om (fun t => γ (Multiplicative.ofAdd t)) Ψ) g h) 0 := by
  first | exact @GlobalTheory.ThK.KernelLineLeft.hasDerivAt_theta_lineLeft | exact GlobalTheory.ThK.KernelLineLeft.hasDerivAt_theta_lineLeft | (intros; apply GlobalTheory.ThK.KernelLineLeft.hasDerivAt_theta_lineLeft <;> assumption)
