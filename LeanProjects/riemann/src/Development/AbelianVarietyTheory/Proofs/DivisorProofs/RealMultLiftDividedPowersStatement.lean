import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealMultLiftDividedPowers
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polynomial_theta_archimedean_lie_action : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hσ : ∀ x, σ (σ x) = x) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), GlobalTheory.ThK.KP → IsTriple B G X om om' →
    ∀ (c : E) (hc : c ≠ 0), σ c = -c → ∀ (w : InfinitePlace F) (τ : EmbOver E w),
      ∃ D : Matrix (Fin (a + a')) (Fin (a + a')) ℂ →ₗ[ℝ] Module.End ℂ ((Fin a × Fin (a + a') → AF F) → ℂ),
        (∀ Z, ∀ Φ ∈ GlobalTheory.ThK.PolData B G.M, D Z Φ ∈ GlobalTheory.ThK.PolData B G.M) ∧
        ∀ (Z : Matrix (Fin (a + a')) (Fin (a + a')) ℂ) (γ : ℝ → GAd σ (c • G.W.J.map σ)),
          (∀ t, embArch σ (c • G.W.J.map σ) w (projArch σ (c • G.W.J.map σ) w (γ t)) = γ t) →
          (∀ t, GlobalTheory.Orb.archMat σ (c • G.W.J.map σ) τ (projArch σ (c • G.W.J.map σ) w (γ t)) = NormedSpace.exp (t • Z)) →
          ∀ Φ ∈ GlobalTheory.ThK.PolData B G.M, ∀ x, HasDerivAt (fun s : ℝ => G.M.I om Φ ((toGAd hσ G.W.J hc).symm (x * γ s)))
            (G.M.I om (D Z Φ) ((toGAd hσ G.W.J hc).symm x)) 0 := by
  first | exact @GlobalTheory.ThKSmoothDer.hasDerivAt_thetaIntegral | exact GlobalTheory.ThKSmoothDer.hasDerivAt_thetaIntegral | (intros; apply GlobalTheory.ThKSmoothDer.hasDerivAt_thetaIntegral <;> assumption)
