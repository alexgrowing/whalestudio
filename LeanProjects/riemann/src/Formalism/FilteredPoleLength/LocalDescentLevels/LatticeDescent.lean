import Formalism.FilteredPoleLength.ReducedBasisBounds.BetaSesquilinearity
import Formalism.LogFactorialIndices.LogProductFormula

noncomputable section

namespace Formalism.LatticeBaseChangeAlt

open Module

namespace LatticeDescentAlt

variable {O K V : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
  [IsFractionRing O K] [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]

theorem span_inf_eq (M : Submodule O V) (hM : Formalism.LatticeIndexTer.IsLat O K V M) (V' : Submodule K V) :
    Submodule.span K ((M ⊓ V'.restrictScalars O : Submodule O V) : Set V) = V' := by
  apply le_antisymm
  · rw [Submodule.span_le]
    intro x hx
    exact hx.2
  · intro v hv
    obtain ⟨d, hd, hdv⟩ := Formalism.LatticeIndexTer.LatticeIndexLength.exists_smul_mem_of_span (K := K) M hM.2 v
    have hd' : (algebraMap O K d) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective O K)).2 hd
    have hmem : d • v ∈ (M ⊓ V'.restrictScalars O : Submodule O V) := by
      refine ⟨hdv, ?_⟩
      show d • v ∈ V'
      rw [← algebraMap_smul K d v]
      exact V'.smul_mem _ hv
    have hsp := Submodule.subset_span (R := K) hmem
    have : v = (algebraMap O K d)⁻¹ • (d • v) := by
      rw [← algebraMap_smul K d v, smul_smul, inv_mul_cancel₀ hd', one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ hsp

theorem fg_inf (M : Submodule O V) (hM : Formalism.LatticeIndexTer.IsLat O K V M) (N : Submodule O V) :
    (M ⊓ N).FG := by
  have : IsNoetherian O M := isNoetherian_of_fg_of_noetherian M hM.1
  have h := IsNoetherian.noetherian (N.comap M.subtype)
  have := h.map M.subtype
  rwa [Submodule.map_comap_subtype] at this

end LatticeDescentAlt

theorem localStepDescent_of (h2 : FinrankSpanImage) (h3 : SpanImageInf) (h4 : RelIndexSpanImage) :
    LocalStepDescent := by
  intro O O' K K' V V₁ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ j hj ϖ hϖ hϖ' M Θ V'
    hM hΘ d Y Z e h
  rw [h3 O O' K K' V V₁ j hj M V' hM, h3 O O' K K' V V₁ j hj Θ V' hΘ,
    h2 O O' K K' V V₁ j hj V',
    h4 O O' K K' V V₁ j hj ϖ hϖ hϖ' _ _ (LatticeDescentAlt.fg_inf M hM _) (LatticeDescentAlt.fg_inf Θ hΘ _)
      (by rw [LatticeDescentAlt.span_inf_eq M hM V', LatticeDescentAlt.span_inf_eq Θ hΘ V'])] at h
  exact h

end Formalism.LatticeBaseChangeAlt
