import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedModelFunctionalEval
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRel
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adapted_model_functional_eval : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d d₁ r s r' s' i₀ i₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (M : Model σ X W)
    (M₁ : Model σ X W₁), B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' → M.IsGood B.ψ → H'.IsAdapted σ B W W₁ i₀ i₁ →
    M₁.IsGood B.ψ → ∀ T : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n × Fin d₁), T ≠ 0 →
    GlobalTheory.ThK.EvUniq.InfRel B M M₁ H' T → Function.Surjective T := by
  first | exact @GlobalTheory.ThK.EvZeroOnto.infRel_onto | exact GlobalTheory.ThK.EvZeroOnto.infRel_onto | (intros; apply GlobalTheory.ThK.EvZeroOnto.infRel_onto <;> assumption)
