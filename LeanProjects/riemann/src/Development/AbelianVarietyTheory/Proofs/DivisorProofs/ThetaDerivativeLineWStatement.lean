import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaDerivativeLineW
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_derivative_line_W : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), GlobalTheory.ThK.KP → IsTriple B G X om om' →
    ∀ γ ∈ Lines σ G.W, ∀ Φ ∈ GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁, ∀ Φ₁ ∈ GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁,
      (∀ x, HasDerivAt (fun t : ℝ => om' (1, γ (Multiplicative.ofAdd t)) Φ x) (Φ₁ x) 0) →
      ∀ h, HasDerivAt (fun t : ℝ => G.M'.I om' Φ (h * γ (Multiplicative.ofAdd t))) (G.M'.I om' Φ₁ h) 0 := by
  first | exact @GlobalTheory.ThetaDerivTriple.hasDerivAt_thetaIntegral_triple | exact GlobalTheory.ThetaDerivTriple.hasDerivAt_thetaIntegral_triple | (intros; apply GlobalTheory.ThetaDerivTriple.hasDerivAt_thetaIntegral_triple <;> assumption)
