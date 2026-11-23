import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairAdaptedPlaneIsPair
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pair_adapted_plane_is_pair : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ) (M₁ : Model σ X W₁) (om₁ : Rep σ X W₁) (r₁ s₁ : ℕ), H'.IsAdapted σ B W W₁ i₀ i₁ → IsPair B M₁ χX χW om₁ r s r₁ s₁ → ∀ (e₀ : Fn F n d →ₗ[ℂ] Fn F n d₁), IsEv B M M₁ 1 H'.ι (iso0 n H') e₀ → ∀ (n₂ d₂ : ℕ) (X₂ : Spc F E n₂) (W₂ : Spc F E d₂) (M₂ : Model σ X₂ W₂) (ι : Matrix (Fin n) (Fin n₂) E) (ι' : Matrix (Fin d) (Fin d₂) E) (I : Set (Matrix (Fin n) (Fin d) (AE F E))) (e : Fn F n d →ₗ[ℂ] Fn F n₂ d₂), M₂.IsGood B.ψ → iso0 n H' ⊆ I → IsEv B M M₂ ι ι' I e → ∀ Φ ∈ schA F (Fin n × Fin d), e₀ Φ = 0 → e Φ = 0 := by
  first | exact @GlobalTheory.EvZeroKer.main | exact GlobalTheory.EvZeroKer.main | (intros; apply GlobalTheory.EvZeroKer.main <;> assumption)
