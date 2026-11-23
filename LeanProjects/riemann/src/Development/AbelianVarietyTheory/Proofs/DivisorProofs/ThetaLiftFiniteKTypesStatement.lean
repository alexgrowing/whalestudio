import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftFiniteKTypes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_lift_finite_K_types : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hσ : ∀ x, σ (σ x) = x) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), GlobalTheory.ThK.KP → IsTriple B G X om om' →
    ∀ (c : E) (hc : c ≠ 0), σ c = -c → ∀ Φ ∈ GlobalTheory.ThK.PolData B G.M,
      ∃ K, IsMaxCpt σ (c • G.W.J.map σ) K ∧ FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : K => fun g => G.M.I om Φ ((toGAd hσ G.W.J hc).symm (g * k)))) := by
  first | exact @GlobalTheory.ThKAutV.KFin.kfin_thetaIntegral | exact GlobalTheory.ThKAutV.KFin.kfin_thetaIntegral | (intros; apply GlobalTheory.ThKAutV.KFin.kfin_thetaIntegral <;> assumption)
