import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineActionDerivativePureTensor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.line_action_derivative_pure_tensor : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    GlobalTheory.ThK.KP → IsTriple B G X om om' → ∀ γ ∈ Lines σ G.W, ∀ f ∈ G.M.Pol B.ψ B.emb,
    ∀ f₁ : SInf F (Fin a × Fin (a + a')), ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) f f₁ →
    ∀ φ : ∀ v : Pl F, (Fin a × Fin (a + a') → Fv F v) → ℂ, (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) →
    (∀ᶠ v in Filter.cofinite, φ v = G.M.vac v) → ∀ g h,
    HasDerivAt (fun s : ℝ => theta om (pure f φ) g (h * γ (Multiplicative.ofAdd s))) (theta om (pure f₁ φ) g h) 0 := by
  first | exact @GlobalTheory.ThKKernelLine.hasDerivAt_theta_line | exact GlobalTheory.ThKKernelLine.hasDerivAt_theta_line | (intros; apply GlobalTheory.ThKKernelLine.hasDerivAt_theta_line <;> assumption)
