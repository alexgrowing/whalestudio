import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaIntegralIteratedRealDerivatives
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CombRSingleNil
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability GlobalTheory.ThK.FiniteLevelDerivatives
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_integral_iterated_real_derivatives : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hσ : ∀ x, σ (σ x) = x) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), GlobalTheory.ThK.KP → IsTriple B G X om om' →
    ∀ (c : E) (hc : c ≠ 0), σ c = -c → ∀ Φ ∈ GlobalTheory.ThK.PolData B G.M,
    ∀ l : List (ℝ → GAd σ (c • G.W.J.map σ)), (∀ γ ∈ l, IsRealLine σ (c • G.W.J.map σ) γ) →
      (l.map (back hσ G.W.J hc)).foldr (derR om) Φ ∈ GlobalTheory.ThK.PolData B G.M ∧
      l.foldr lineDer (fun x => G.M.I om Φ ((toGAd hσ G.W.J hc).symm x)) =
        fun x => G.M.I om ((l.map (back hσ G.W.J hc)).foldr (derR om) Φ) ((toGAd hσ G.W.J hc).symm x) := by
  first | exact @GlobalTheory.ThK.ZFinDer.derivs | exact GlobalTheory.ThK.ZFinDer.derivs | (intros; apply GlobalTheory.ThK.ZFinDer.derivs <;> assumption)
