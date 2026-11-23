import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftInvariantRationalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenSubgroupInvariantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousThetaLiftTransferStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftRealLineDerivativeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftBoundedDerivativesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftFiniteKTypesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftFiniteCenterSpanStatement

open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability

namespace GlobalTheory.ThKAutV

theorem isAut_thetaIntegral : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hσ : ∀ x, σ (σ x) = x) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), GlobalTheory.ThK.KP → IsTriple B G X om om' →
    ∀ (c : E) (hc : c ≠ 0), σ c = -c → ∀ Φ ∈ GlobalTheory.ThK.PolData B G.M,
      ∃ K, IsMaxCpt σ (c • G.W.J.map σ) K ∧
        IsAut σ (c • G.W.J.map σ) K (fun x => G.M.I om Φ ((toGAd hσ G.W.J hc).symm x)) := by
  intro F E _ _ _ _ _ σ hσ B a a' G X om om' hK hT c hc hcc Φ hΦ
  obtain ⟨K, hKm, hKf⟩ := GlobalTheory.T.theta_lift_finite_K_types F E σ hσ B a a' G X om om' hK hT c hc hcc Φ hΦ
  exact ⟨K, hKm, ⟨⟨GlobalTheory.T.theta_lift_invariant_rational F E σ hσ B a a' G X om om' hK hT c hc hcc Φ hΦ, GlobalTheory.T.exists_open_subgroup_invariant F E σ hσ B a a' G X om om' hK hT c hc hcc Φ hΦ,
    GlobalTheory.T.continuous_theta_lift_transfer F E σ hσ B a a' G X om om' hK hT c hc hcc Φ hΦ, GlobalTheory.T.theta_lift_real_line_derivative F E σ hσ B a a' G X om om' hK hT c hc hcc Φ hΦ,
    GlobalTheory.T.theta_lift_lineDer_uniform_moderate_growth F E σ hσ B a a' G X om om' hK hT c hc hcc Φ hΦ⟩, hKf, GlobalTheory.T.theta_lift_finite_center_span F E σ hσ B a a' G X om om' hK hT c hc hcc Φ hΦ⟩⟩

end GlobalTheory.ThKAutV
