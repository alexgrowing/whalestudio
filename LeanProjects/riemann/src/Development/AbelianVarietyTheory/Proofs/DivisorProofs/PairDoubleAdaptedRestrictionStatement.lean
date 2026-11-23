import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairDoubleAdaptedRestriction
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pair_double_adapted_restriction : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d n₁ d₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (X₁ : Spc F E n₁) (W₁ : Spc F E d₁) (M : Model σ X W) (χX χW : Chr F E)
    (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (H : Plane E n n₁) (H' : Plane E d d₁) (j₀ j₁ i₀ i₁ : ℕ) (M₁ : Model σ X₁ W₁) (om₁ : Rep σ X₁ W₁) (r₁ s₁ r₁' s₁' : ℕ),
    H.IsAdapted σ B X X₁ j₀ j₁ → H'.IsAdapted σ B W W₁ i₀ i₁ → IsPair B M₁ χX χW om₁ r₁ s₁ r₁' s₁' →
    ∀ e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁, IsEv B M M₁ H.ι H'.ι (isoA H H') e →
    ∀ (l : (AE F E)ˣ) (g₀ : UA σ X₁.J) (m : UA σ X.J), IsLevi (W₁ := X₁) H l g₀ m →
    ∀ c : ℂ, (∀ Φ ∈ schA F (Fin n × Fin d), e (om (m, 1) Φ) = c • om₁ (g₀, 1) (e Φ)) →
      ‖c‖ = (absE F E l : ℝ) ^ ((d₁ : ℝ) / 2) := by
  first | exact @GlobalTheory.ThK.LeviModulus.norm_const_eq | exact GlobalTheory.ThK.LeviModulus.norm_const_eq | (intros; apply GlobalTheory.ThK.LeviModulus.norm_const_eq <;> assumption)
