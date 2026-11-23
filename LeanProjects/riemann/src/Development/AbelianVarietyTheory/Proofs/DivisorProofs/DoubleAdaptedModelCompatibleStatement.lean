import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubleAdaptedModelCompatible
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRelG
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.double_adapted_model_compatible : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d n₁ d₁ r s r' s' i₀ i₁ j₀ j₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (X₁ : Spc F E n₁) (W₁ : Spc F E d₁) (H : Plane E n n₁)
    (H' : Plane E d d₁) (M : Model σ X W) (M₁ : Model σ X₁ W₁), B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' →
    M.IsGood B.ψ → H.IsAdapted σ B X X₁ j₀ j₁ → H'.IsAdapted σ B W W₁ i₀ i₁ → M₁.IsGood B.ψ →
    ∀ (v : Pl F) (T T' : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Fin n₁ × Fin d₁ → Fv F v) → ℂ),
    GlobalTheory.ThK.EvFactor.FinRelG B M M₁ H.ι H'.ι (isoA H H') v T → GlobalTheory.ThK.EvFactor.FinRelG B M M₁ H.ι H'.ι (isoA H H') v T' →
    (SB _).map T = SB _ → (SB _).map T' = SB _ → T (M.vac v) = M₁.vac v → T' (M.vac v) = M₁.vac v →
    ∀ φ ∈ SB (Fin n × Fin d → Fv F v), T' φ = T φ := by
  first | exact @GlobalTheory.ThK.EvUniqA.finRelG_isoA_unique | exact GlobalTheory.ThK.EvUniqA.finRelG_isoA_unique | (intros; apply GlobalTheory.ThK.EvUniqA.finRelG_isoA_unique <;> assumption)
