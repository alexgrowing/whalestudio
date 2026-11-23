import Mathlib
open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace GlobalTheory

theorem shrink_nbhd_generise_centre : ∀ (X : Scheme.{0}) [IsLocallyNoetherian X] (P : X → Prop) (G : Set X),
    IsOpen G → ∀ (U : X.Opens) (z : X), z ∈ U → (∀ q ∈ U, P q → ∀ η : X, η ⤳ q → η ≠ q → η ∈ G) →
      ∃ V : X.Opens, V ≤ U ∧ z ∈ V ∧ ∀ q ∈ V, P q → q ∈ G ∨ q ⤳ z := by
  intro X _ P G hG U z hzU hgen
  obtain ⟨U', hU', hzU', hU'U⟩ := (Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens) hzU
  have : IsNoetherianRing Γ(X, U') := IsLocallyNoetherian.component_noetherian ⟨U', hU'⟩
  haveI hN : NoetherianSpace (U' : Set X) := noetherianSpace_of_isAffineOpen U' hU'

  have hC : IsClosed {x : (U' : Set X) | (x : X) ∉ G} := (hG.preimage continuous_subtype_val).isClosed_compl
  obtain ⟨S, hS, hSc, hSi, hSeq⟩ := NoetherianSpace.exists_finite_set_isClosed_irreducible hC
  let F : Set (Set (U' : Set X)) := {T | T ∈ S ∧ z ∉ closure (Subtype.val '' T)}
  have hF : F.Finite := hS.subset (fun T hT => hT.1)
  let K : Set X := ⋃ T ∈ F, closure (Subtype.val '' T)
  have hK : IsClosed K := hF.isClosed_biUnion (fun _ _ => isClosed_closure)
  refine ⟨⟨(U' : Set X) ∩ Kᶜ, U'.isOpen.inter hK.isOpen_compl⟩, ?_, ?_, ?_⟩
  · exact fun x hx => hU'U hx.1
  · refine ⟨hzU', ?_⟩
    simp only [K, Set.mem_compl_iff, Set.mem_iUnion, not_exists]
    exact fun T hT => hT.2
  · rintro q ⟨hqU', hqK⟩ hPq
    by_cases hqG : q ∈ G
    · exact Or.inl hqG
    right
    have hqC : (⟨q, hqU'⟩ : (U' : Set X)) ∈ ⋃₀ S := by rw [← hSeq]; exact hqG
    obtain ⟨T, hTS, hqT⟩ := hqC
    have hzT : z ∈ closure (Subtype.val '' T) := by
      by_contra hz
      exact hqK (Set.mem_biUnion (x := T) ⟨hTS, hz⟩ (subset_closure ⟨_, hqT, rfl⟩))
    have hirr : IsIrreducible (Subtype.val '' T) := (hSi T hTS).image _ continuous_subtype_val.continuousOn
    obtain ⟨c, hc⟩ := QuasiSober.sober hirr.closure isClosed_closure

    have hcU' : c ∈ (U' : Set X) := (hc.mem_open_set_iff U'.isOpen).mpr
      ⟨q, subset_closure ⟨_, hqT, rfl⟩, hqU'⟩
    have hcG : c ∉ G := by
      have hsub : closure (Subtype.val '' T) ⊆ Gᶜ := closure_minimal
        (by rintro _ ⟨x, hx, rfl⟩; have := hSeq ▸ (Set.subset_sUnion_of_mem hTS hx); exact this) hG.isClosed_compl
      exact hsub hc.mem
    have hcq : c ⤳ q := hc.specializes (subset_closure ⟨_, hqT, rfl⟩)
    by_cases hne : c = q
    · subst hne
      exact hc.specializes hzT
    · exact absurd (hgen q (hU'U hqU') hPq c hcq hne) hcG

end GlobalTheory
