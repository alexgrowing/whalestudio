import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigFirstEvalCharCompat
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPairOfIsTriple

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.config_first_eval_char_compat : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a')
    (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' → ∀ e, IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e →
    ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W), IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ e' : Fn F (b + 2) (b + 2 + a') →ₗ[ℂ] Fn F b (b + a'),
    (∀ z, ∀ Φ ∈ schA F (Fin (b + 2) × Fin (b + 2 + a')), e' (G.M.co.rho B.ψ (incM F H.ι * z * (incM F H'.ι)ᵀ) Φ) = G₁.M.co.rho B.ψ z (e' Φ)) →
    (∀ u ∈ isoA (F := F) H H', ∀ Φ ∈ schA F (Fin (b + 2) × Fin (b + 2 + a')), e' (G.M.co.rho B.ψ u Φ) = e' Φ) →
    (∀ y : Fin b × Fin (b + a') → AF F, (LinearMap.proj y : Fn F b (b + a') →ₗ[ℂ] ℂ) ∘ₗ e' ∈ (adeleClass F).adm (Fin (b + 2) × Fin (b + 2 + a'))) →
    ∃ c : ℂ, ∀ Φ ∈ schA F (Fin (b + 2) × Fin (b + 2 + a')), e' Φ = c • e Φ := by
  first | exact @GlobalTheory.ThKUniqA.main | exact GlobalTheory.ThKUniqA.main | (intros; apply GlobalTheory.ThKUniqA.main <;> assumption)
