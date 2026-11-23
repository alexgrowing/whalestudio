import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolDataThetaLinear
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pol_data_theta_linear : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    GlobalTheory.ThK.KP → IsTriple B G X om om' →
      ∃ L : ↥(GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁) →ₗ[ℂ] (UA σ G.W.J → ℂ),
        ∀ Φ : ↥(GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁), L Φ = G.M'.I om' Φ := by
  first | exact @GlobalTheory.ThKLinT.thetaIntegral_linear_of_triple | exact GlobalTheory.ThKLinT.thetaIntegral_linear_of_triple | (intros; apply GlobalTheory.ThKLinT.thetaIntegral_linear_of_triple <;> assumption)
