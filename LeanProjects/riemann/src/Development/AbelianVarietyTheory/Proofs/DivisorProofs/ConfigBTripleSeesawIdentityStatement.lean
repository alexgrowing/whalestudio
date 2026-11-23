import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBTripleSeesawIdentity
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.config_b_triple_seesaw_identity : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ) (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' → ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W), IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' → ∀ (V₂ : Spc F E a) (n₁ : ℕ) (X₁ : Spc F E n₁) (H₀ : Plane E a n₁) (j₀ j₁ : ℕ) (M₂ : Model σ X₁ G₁.W) (e₂ : Fn F a (a + (b + 2)) →ₗ[ℂ] Fn F n₁ (a + b)), (reS G.V V₂).IsHerm σ B (a - G.p) G.p → H₀.IsAdapted σ B (reS G.V V₂) X₁ j₀ j₁ → M₂.IsGood B.ψ → IsEv B G.M M₂ H₀.ι H'.ι (isoA H₀ H') e₂ →
    ∀ e' : Fn F a (a + (b + 2)) →ₗ[ℂ] Fn F n₁ (a + b),
    (∀ z, ∀ Φ ∈ schA F (Fin a × Fin (a + (b + 2))), e' (G.M.co.rho B.ψ (incM F H₀.ι * z * (incM F H'.ι)ᵀ) Φ) = M₂.co.rho B.ψ z (e' Φ)) →
    (∀ u ∈ isoA (F := F) H₀ H', ∀ Φ ∈ schA F (Fin a × Fin (a + (b + 2))), e' (G.M.co.rho B.ψ u Φ) = e' Φ) →
    (∀ y : Fin n₁ × Fin (a + b) → AF F, (LinearMap.proj y : Fn F n₁ (a + b) →ₗ[ℂ] ℂ) ∘ₗ e' ∈ (adeleClass F).adm (Fin a × Fin (a + (b + 2)))) →
    ∃ c : ℂ, ∀ Φ ∈ schA F (Fin a × Fin (a + (b + 2))), e' Φ = c • e₂ Φ := by
  first | exact @GlobalTheory.TwoPlaneUniq.main | exact GlobalTheory.TwoPlaneUniq.main | (intros; apply GlobalTheory.TwoPlaneUniq.main <;> assumption)
