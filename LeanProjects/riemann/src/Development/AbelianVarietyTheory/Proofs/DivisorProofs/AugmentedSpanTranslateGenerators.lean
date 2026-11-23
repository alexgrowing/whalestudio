import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearBarGlHaarIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearBarSpanGlIntegralStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical

namespace GlobalTheory.CoinvFullRank

theorem mem_span_diff_of_mem_augAt : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ x ∈ augAt om' B.v₁, x ∈ Submodule.span ℂ (G.M'.SoLoc B.ψ B.τ₁) →
      x ∈ Submodule.span ℂ {y | ∃ g ∈ UAt σ G.V' (evFin F B.v₁), ∃ ψ ∈ G.M'.SoLoc B.ψ B.τ₁, ∃ ψ' ∈ G.M'.SoLoc B.ψ B.τ₁,
        Acts (evFin F B.v₁) (om' (g, 1)) ψ ψ' ∧ y = ψ' - ψ} := by
  intro hK F E _ _ _ _ _ σ B a a' G X om om' hT x hx hxS
  by_cases hS : ∃ ψ, ψ ∈ G.M'.SoLoc B.ψ B.τ₁
  · obtain ⟨ψ, -, ι, hι, -⟩ := hS
    exact GlobalTheory.T.linear_bar_span_gl_integral hK F E σ B a a' G X om om' hT ι hι x hxS
      (fun μ _ Y hY => GlobalTheory.T.linear_bar_gl_haar_integral hK F E σ B a a' G X om om' hT ι hι μ x hx Y hY)
  · have h0 : G.M'.SoLoc B.ψ B.τ₁ = ∅ := Set.eq_empty_iff_forall_notMem.2 fun ψ h => hS ⟨ψ, h⟩
    rw [h0, Submodule.span_empty, Submodule.mem_bot] at hxS
    subst hxS
    exact zero_mem _

end GlobalTheory.CoinvFullRank
