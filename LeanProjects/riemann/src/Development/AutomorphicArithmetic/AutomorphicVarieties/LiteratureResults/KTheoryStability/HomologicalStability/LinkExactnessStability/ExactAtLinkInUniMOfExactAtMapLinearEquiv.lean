import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LinkExactAff
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.SeqChainExactAtMapIff

open GlobalTheory.SeqCx Matrix

namespace GlobalTheory.SeqCxLinkEquiv

theorem uniM_map_of_mem {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (ψ : M ≃ₗ[R] M)
    (l : List M) (h : l ∈ uniM R M) : l.map ψ ∈ uniM R M := by
  obtain ⟨f, hf⟩ := h
  have hl : (l.map ψ).length = l.length := by simp
  refine ⟨fun i => (f (Fin.cast hl i)).comp ψ.symm.toLinearMap, ?_⟩
  intro i j
  have := hf (Fin.cast hl i) (Fin.cast hl j)
  simpa [Fin.ext_iff] using this

theorem linkIn_map {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (ψ : M ≃ₗ[R] M)
    (X : Set M) (hX : ∀ x, ψ x ∈ X ↔ x ∈ X) (τ : List M) :
    linkIn (uniM R M) X (τ.map ψ) = List.map ψ '' linkIn (uniM R M) X τ := by
  ext w
  simp only [linkIn, Set.mem_setOf_eq, Set.mem_image]
  constructor
  · rintro ⟨hw, hmem⟩
    refine ⟨w.map ψ.symm, ⟨?_, ?_⟩, ?_⟩
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
      rw [← hX]
      simpa using hw y hy
    · have := uniM_map_of_mem ψ.symm _ hmem
      simpa [List.map_append, List.map_map, Function.comp_def] using this
    · simp [List.map_map, Function.comp_def]
  · rintro ⟨w', ⟨hw', hmem⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
      exact (hX y).2 (hw' y hy)
    · have := uniM_map_of_mem ψ _ hmem
      simpa [List.map_append] using this

private theorem bd_mapDomain_listMap_comm {V : Type} (g : V → V) (c : List V →₀ ℤ) :
    bd V (Finsupp.mapDomain (List.map g) c) = Finsupp.mapDomain (List.map g) (bd V c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => simp [Finsupp.mapDomain_add, ha, hb]
  | single l n =>
    simp [bd, Finsupp.mapDomain_single, Finsupp.linearCombination_single,
      Finsupp.mapDomain_finset_sum, Finsupp.mapDomain_smul, List.eraseIdx_map]

private theorem mapDomain_listMap_mem_chains_of_map_mem {V : Type} (g : V → V) (F G : Set (List V))
    (hFG : ∀ l ∈ F, l.map g ∈ G) (p : ℕ) (c : List V →₀ ℤ) (hc : c ∈ chains F p) :
    Finsupp.mapDomain (List.map g) c ∈ chains G p := by
  classical
  rw [chains, Finsupp.mem_supported] at hc ⊢
  intro x hx
  obtain ⟨l, hl, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hx)
  obtain ⟨hlF, hlen⟩ := hc hl
  exact ⟨hFG l hlF, by simp [hlen]⟩

theorem exactAt_linkIn_of_map : ∀ (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] (ψ : M ≃ₗ[R] M) (X : Set M), (∀ x, ψ x ∈ X ↔ x ∈ X) → ∀ (τ : List M) (p : ℕ), ExactAt (linkIn (uniM R M) X (τ.map ψ)) p → ExactAt (linkIn (uniM R M) X τ) p := by
  intro R M _ _ _ ψ X hX τ p h
  rw [linkIn_map ψ X hX τ] at h
  intro c hc hbd
  have hc' := mapDomain_listMap_mem_chains_of_map_mem (⇑ψ) (linkIn (uniM R M) X τ)
    (List.map ψ '' linkIn (uniM R M) X τ) (fun l hl => ⟨l, hl, rfl⟩) p c hc
  obtain ⟨b, hb, hbb⟩ := h _ hc' (by rw [bd_mapDomain_listMap_comm, hbd]; simp)
  refine ⟨Finsupp.mapDomain (List.map ψ.symm) b,
    mapDomain_listMap_mem_chains_of_map_mem (⇑ψ.symm) _ _ ?_ _ b hb, ?_⟩
  · rintro _ ⟨l, hl, rfl⟩
    simpa [List.map_map, Function.comp_def] using hl
  · have hid : (List.map ψ.symm ∘ List.map ψ) = id := by
      funext l
      simp [List.map_map, Function.comp_def]
    rw [bd_mapDomain_listMap_comm, hbb, ← Finsupp.mapDomain_comp, hid, Finsupp.mapDomain_id]

end GlobalTheory.SeqCxLinkEquiv

section
open GlobalTheory.SeqCx Matrix
theorem _root_.GlobalTheory.T.exactAt_linkIn_uniM_of_exactAt_map_linearEquiv : ∀ (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] (ψ : M ≃ₗ[R] M) (X : Set M), (∀ x, ψ x ∈ X ↔ x ∈ X) → ∀ (τ : List M) (p : ℕ), ExactAt (linkIn (uniM R M) X (τ.map ψ)) p → ExactAt (linkIn (uniM R M) X τ) p := by
  first
  | exact @GlobalTheory.SeqCxLinkEquiv.exactAt_linkIn_of_map
  | exact @GlobalTheory.SeqCxLinkEquiv.linkIn_map
  | exact @GlobalTheory.SeqCxLinkEquiv.uniM_map_of_mem
end
