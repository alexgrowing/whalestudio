import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftPolynomialGrowthBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_lift_polynomial_growth_bound : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hσ : ∀ x, σ (σ x) = x) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), GlobalTheory.ThK.KP → IsTriple B G X om om' →
    ∀ (c : E) (hc : c ≠ 0), σ c = -c →
    ∃ N : ℕ, ∀ Φ ∈ GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁, ∃ C : ℝ, ∀ g : GAd σ (c • G.W.J.map σ),
      ‖G.M'.I om' Φ ((toGAd hσ G.W.J hc).symm g)‖ ≤ C * (height σ (c • G.W.J.map σ) g : ℝ) ^ N := by
  first | exact @GlobalTheory.ThKGrowthSmallBd.growth_bd | exact GlobalTheory.ThKGrowthSmallBd.growth_bd | (intros; apply GlobalTheory.ThKGrowthSmallBd.growth_bd <;> assumption)
