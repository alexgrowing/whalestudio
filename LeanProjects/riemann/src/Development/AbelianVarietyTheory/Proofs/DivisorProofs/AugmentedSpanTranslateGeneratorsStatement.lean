import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AugmentedSpanTranslateGenerators
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.augmented_span_translate_generators : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ x ∈ augAt om' B.v₁, x ∈ Submodule.span ℂ (G.M'.SoLoc B.ψ B.τ₁) →
      x ∈ Submodule.span ℂ {y | ∃ g ∈ UAt σ G.V' (evFin F B.v₁), ∃ ψ ∈ G.M'.SoLoc B.ψ B.τ₁, ∃ ψ' ∈ G.M'.SoLoc B.ψ B.τ₁,
        Acts (evFin F B.v₁) (om' (g, 1)) ψ ψ' ∧ y = ψ' - ψ} := by
  first | exact @GlobalTheory.CoinvFullRank.mem_span_diff_of_mem_augAt | exact GlobalTheory.CoinvFullRank.mem_span_diff_of_mem_augAt | (intros; apply GlobalTheory.CoinvFullRank.mem_span_diff_of_mem_augAt <;> assumption)
