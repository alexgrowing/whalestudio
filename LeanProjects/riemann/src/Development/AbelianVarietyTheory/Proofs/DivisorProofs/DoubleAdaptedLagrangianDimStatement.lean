import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubleAdaptedLagrangianDim
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRelG
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.double_adapted_lagrangian_dim : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d n₁ d₁ r s r' s' i₀ i₁ j₀ j₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (X₁ : Spc F E n₁) (W₁ : Spc F E d₁) (H : Plane E n n₁)
    (H' : Plane E d d₁) (M : Model σ X W) (M₁ : Model σ X₁ W₁), B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' →
    M.IsGood B.ψ → H.IsAdapted σ B X X₁ j₀ j₁ → H'.IsAdapted σ B W W₁ i₀ i₁ → M₁.IsGood B.ψ →
    ∀ T T' : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n₁ × Fin d₁), T ≠ 0 →
    GlobalTheory.ThK.EvFactor.InfRelG B M M₁ H.ι H'.ι (isoA H H') T → GlobalTheory.ThK.EvFactor.InfRelG B M M₁ H.ι H'.ι (isoA H H') T' →
    ∃ c : ℂ, T' = c • T := by
  first | exact @GlobalTheory.ArchSchA.infRelA_proportional | exact GlobalTheory.ArchSchA.infRelA_proportional | (intros; apply GlobalTheory.ArchSchA.infRelA_proportional <;> assumption)
