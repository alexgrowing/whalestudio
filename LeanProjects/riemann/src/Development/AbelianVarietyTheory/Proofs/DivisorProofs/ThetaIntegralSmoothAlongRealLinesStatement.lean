import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaIntegralSmoothAlongRealLines
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_integral_smooth_along_real_lines : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hσ : ∀ x, σ (σ x) = x) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), GlobalTheory.ThK.KP → IsTriple B G X om om' →
    ∀ (c : E) (hc : c ≠ 0), σ c = -c →
    ∀ Φ ∈ GlobalTheory.ThK.PolData B G.M, ∀ γ : ℝ → GAd σ (c • G.W.J.map σ), IsRealLine σ (c • G.W.J.map σ) γ →
      ∃ Φ₁ ∈ GlobalTheory.ThK.PolData B G.M, lineDer γ (fun x => G.M.I om Φ ((toGAd hσ G.W.J hc).symm x)) =
        fun x => G.M.I om Φ₁ ((toGAd hσ G.W.J hc).symm x) := by
  first | exact @GlobalTheory.ThKDer.lineDer_thetaIntegral | exact GlobalTheory.ThKDer.lineDer_thetaIntegral | (intros; apply GlobalTheory.ThKDer.lineDer_thetaIntegral <;> assumption)
