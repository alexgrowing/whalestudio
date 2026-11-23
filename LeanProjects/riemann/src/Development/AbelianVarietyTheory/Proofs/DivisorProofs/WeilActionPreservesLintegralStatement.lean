import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilActionPreservesLintegral
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_action_preserves_lintegral : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n d : ℕ) (X : Spc F E n)
    (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W), M.IsWeil ψ χX χW om →
    ∀ (x : UA σ X.J × UA σ W.J) (f f₁ : SInf F (Fin n × Fin d)), Acts (evI F) (om x) (⇑f) (⇑f₁) →
      ∀ μ : Measure (Fin n × Fin d → mixedEmbedding.mixedSpace F), μ.IsAddHaarMeasure →
        ∫⁻ y, ‖f₁ y‖ₑ ^ 2 ∂μ = ∫⁻ y, ‖f y‖ₑ ^ 2 ∂μ := by
  first | exact @GlobalTheory.ArchimedeanActsL2.acts_lintegral_eq | exact GlobalTheory.ArchimedeanActsL2.acts_lintegral_eq | (intros; apply GlobalTheory.ArchimedeanActsL2.acts_lintegral_eq <;> assumption)
