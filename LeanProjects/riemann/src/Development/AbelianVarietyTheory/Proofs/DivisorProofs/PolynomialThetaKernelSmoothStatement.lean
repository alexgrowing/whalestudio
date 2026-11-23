import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialThetaKernelSmooth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polynomial_theta_kernel_smooth : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hσ : ∀ x, σ (σ x) = x) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), GlobalTheory.ThK.KP → IsTriple B G X om om' →
    ∀ (c : E) (hc : c ≠ 0), σ c = -c → ∀ Φ ∈ GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁,
      IsSm σ (c • G.W.J.map σ) (fun x => G.M'.I om' Φ ((toGAd hσ G.W.J hc).symm x)) := by
  first | exact @GlobalTheory.ThAutSmall.Smooth.isSm_theta_small | exact GlobalTheory.ThAutSmall.Smooth.isSm_theta_small | (intros; apply GlobalTheory.ThAutSmall.Smooth.isSm_theta_small <;> assumption)
