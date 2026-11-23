import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftRealLineDerivative
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_lift_real_line_derivative : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hσ : ∀ x, σ (σ x) = x) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), GlobalTheory.ThK.KP → IsTriple B G X om om' →
    ∀ (c : E) (hc : c ≠ 0), σ c = -c → ∀ Φ ∈ GlobalTheory.ThK.PolData B G.M,
      ∀ (k : ℕ) (γ : Fin k → ℝ → GAd σ (c • G.W.J.map σ)), (∀ i, IsRealLine σ (c • G.W.J.map σ) (γ i)) → ∀ g, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun t : Fin k → ℝ => G.M.I om Φ ((toGAd hσ G.W.J hc).symm (g * (List.ofFn fun i => γ i (t i)).prod)) := by
  first | exact @GlobalTheory.ThKAutV.Smooth.contDiff_lines | exact GlobalTheory.ThKAutV.Smooth.contDiff_lines | (intros; apply GlobalTheory.ThKAutV.Smooth.contDiff_lines <;> assumption)
