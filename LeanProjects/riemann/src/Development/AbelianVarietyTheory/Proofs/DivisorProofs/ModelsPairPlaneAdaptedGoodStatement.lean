import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelsPairPlaneAdaptedGood
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.models_pair_plane_adapted_good : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d n₁ d₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (X₁ : Spc F E n₁) (W₁ : Spc F E d₁) (M : Model σ X W) (M₂ : Model σ X₁ W₁)
    (H : Plane E n n₁) (H' : Plane E d d₁) (i₀ i₁ j₀ j₁ : ℕ), B.IsGood σ → (∃ r s r' s' : ℕ, X.IsHerm σ B r s ∧ W.IsSkew σ B r' s') →
    M.IsGood B.ψ → M₂.IsGood B.ψ → H.IsAdapted σ B X X₁ j₀ j₁ → H'.IsAdapted σ B W W₁ i₀ i₁ →
    ∀ e e₂ : Fn F n d →ₗ[ℂ] Fn F n₁ d₁, IsEv B M M₂ H.ι H'.ι (isoA H H') e → IsEv B M M₂ H.ι H'.ι (isoA H H') e₂ →
      ∃ c : ℂ, ∀ Ψ ∈ schA F (Fin n × Fin d), e₂ Ψ = c • e Ψ := by
  first | exact @GlobalTheory.ThK.IsoUniq.main | exact GlobalTheory.ThK.IsoUniq.main | (intros; apply GlobalTheory.ThK.IsoUniq.main <;> assumption)
