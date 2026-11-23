import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CotInd

open IsLocalRing UpperTheory.V.AlgebraTools

theorem UpperTheory.V.AlgebraTools.cotInd_of_span :
    ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (κ : Type) [Fintype κ] (x : κ → R),
      Ideal.span (Set.range x) = maximalIdeal R → Fintype.card κ ≤ (maximalIdeal R).spanFinrank → CotInd R x := by
  intro R _ _ _ κ _ x hx hcard
  have hm : ∀ k, x k ∈ maximalIdeal R := fun k => hx ▸ Ideal.subset_span ⟨k, rfl⟩
  refine (cotInd_iff R x).mpr ⟨hm, ?_⟩
  let g : κ → maximalIdeal R := fun k => ⟨x k, hm k⟩
  have hg : Submodule.span R (Set.range g) = ⊤ := by
    apply Submodule.map_injective_of_injective (maximalIdeal R).injective_subtype
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp]
    exact hx
  have hV : Submodule.span (ResidueField R) (Set.range ((maximalIdeal R).toCotangent ∘ g)) = ⊤ := by
    rw [Set.range_comp, CotangentSpace.span_image_eq_top_iff]
    exact hg
  have hfg : (maximalIdeal R).FG := IsNoetherian.noetherian _
  have hle := finrank_range_le_card (R := ResidueField R) ((maximalIdeal R).toCotangent ∘ g)
  rw [Set.finrank, hV, finrank_top] at hle
  rw [spanFinrank_maximalIdeal_eq_finrank_cotangentSpace_of_fg hfg] at hcard
  exact linearIndependent_of_top_le_span_of_card_eq_finrank hV.ge (le_antisymm hcard hle)
