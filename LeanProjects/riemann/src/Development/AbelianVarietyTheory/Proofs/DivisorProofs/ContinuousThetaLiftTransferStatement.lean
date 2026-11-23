import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousThetaLiftTransfer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_theta_lift_transfer : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hσ : ∀ x, σ (σ x) = x) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), GlobalTheory.ThK.KP → IsTriple B G X om om' →
    ∀ (c : E) (hc : c ≠ 0), σ c = -c → ∀ Φ ∈ GlobalTheory.ThK.PolData B G.M,
      Continuous (fun x => G.M.I om Φ ((toGAd hσ G.W.J hc).symm x)) := by
  first | exact @GlobalTheory.ThK.SquareIntegrability.continuous_I_toGAd | exact GlobalTheory.ThK.SquareIntegrability.continuous_I_toGAd | (intros; apply GlobalTheory.ThK.SquareIntegrability.continuous_I_toGAd <;> assumption)
