import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftBoundedDerivatives
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_lift_lineDer_uniform_moderate_growth : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hσ : ∀ x, σ (σ x) = x) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), GlobalTheory.ThK.KP → IsTriple B G X om om' →
    ∀ (c : E) (hc : c ≠ 0), σ c = -c → ∀ Φ ∈ GlobalTheory.ThK.PolData B G.M,
      ∃ N : ℕ, ∀ l : List (ℝ → GAd σ (c • G.W.J.map σ)), (∀ γ ∈ l, IsRealLine σ (c • G.W.J.map σ) γ) → ∃ C : ℝ, ∀ g, ‖l.foldr lineDer (fun x => G.M.I om Φ ((toGAd hσ G.W.J hc).symm x)) g‖ ≤ C * (height σ (c • G.W.J.map σ) g : ℝ) ^ N := by
  first | exact @GlobalTheory.ThKAutVGrowth.uniformGrowth_thetaIntegral | exact GlobalTheory.ThKAutVGrowth.uniformGrowth_thetaIntegral | (intros; apply GlobalTheory.ThKAutVGrowth.uniformGrowth_thetaIntegral <;> assumption)
