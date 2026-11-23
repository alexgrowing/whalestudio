import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableOnSqFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integrableOn_sq_fundamental_domain : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hσ : ∀ x, σ (σ x) = x) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (c : E) (hc : c ≠ 0)
    (φ : GAd σ (c • J.map σ) → ℂ), IsSqInt σ (c • J.map σ) φ →
    ∀ (μ : Measure (UA σ J)) (𝓕 : Set (UA σ J)), μ.IsHaarMeasure → IsFundamentalDomain (ratU σ J) 𝓕 μ →
      IntegrableOn (fun h => ‖φ (toGAd hσ J hc h)‖ ^ 2) 𝓕 μ := by
  first | exact @GlobalTheory.ThK.SquareIntegrability.isSqInt_transport | exact GlobalTheory.ThK.SquareIntegrability.isSqInt_transport | (intros; apply GlobalTheory.ThK.SquareIntegrability.isSqInt_transport <;> assumption)
