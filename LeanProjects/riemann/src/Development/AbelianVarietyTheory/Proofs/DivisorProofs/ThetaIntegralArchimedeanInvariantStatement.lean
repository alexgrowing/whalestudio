import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaIntegralArchimedeanInvariant
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_integral_archimedean_invariant : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' → ∀ g ∈ UAt σ X (evI F), ∀ (h : UA σ W.J) (Φ : (Fin n × Fin d → AF F) → ℂ),
      Φ ∈ schA F (Fin n × Fin d) → ∀ y, M.I om (om (g, h) Φ) y = M.I om Φ (y * h) := by
  first | exact @GlobalTheory.ThetaRightTranslate.thetaIntegral_translate | exact GlobalTheory.ThetaRightTranslate.thetaIntegral_translate | (intros; apply GlobalTheory.ThetaRightTranslate.thetaIntegral_translate <;> assumption)
