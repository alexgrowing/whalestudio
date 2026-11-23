import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory

theorem finprod_eq_finprod_mem_fibres_of_section :
    ∀ {α γ M : Type} [CommMonoid M] (p : α → γ) (S : Set α) (f : α → M),
      (∀ x, ∃! s, s ∈ S ∧ p s = p x) → (Function.mulSupport f).Finite →
        ∏ᶠ x, f x = ∏ᶠ s ∈ S, ∏ᶠ x ∈ {x | p x = p s}, f x := by
  intro α γ M _ p S f hS hf
  choose g hg using fun x => (hS x).exists
  have key : ∀ s ∈ S, ∀ x, p x = p s ↔ g x = s := by
    intro s hs x
    constructor
    · intro h
      exact (hS x).unique (hg x) ⟨hs, h.symm⟩
    · rintro rfl
      exact (hg x).2.symm
  set T := hf.toFinset with hT
  have hin : ∀ s ∈ S, ∏ᶠ x ∈ {x | p x = p s}, f x = ∏ x ∈ T with g x = s, f x := by
    intro s hs
    apply finprod_mem_eq_prod_of_subset
    · rintro x ⟨hx1, hx2⟩
      simp only [Finset.coe_filter, Set.mem_setOf_eq, hT, Set.Finite.mem_toFinset]
      exact ⟨hx2, (key s hs x).1 hx1⟩
    · intro x hx
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hx
      exact (key s hs x).2 hx.2
  rw [finprod_mem_congr rfl hin, finprod_eq_prod_of_mulSupport_subset f (s := T) (by simp [hT])]
  rw [finprod_mem_eq_prod_of_subset (t := T.image g)]
  · exact (Finset.prod_fiberwise_of_maps_to (fun i hi => Finset.mem_image_of_mem g hi) f).symm
  · rintro s ⟨_, hs⟩
    rw [Function.mem_mulSupport] at hs
    obtain ⟨u, hu, _⟩ := Finset.exists_ne_one_of_prod_ne_one hs
    rw [Finset.mem_filter] at hu
    rw [Finset.coe_image]
    exact ⟨u, hu.1, hu.2⟩
  · intro s hs
    rw [Finset.coe_image] at hs
    obtain ⟨u, _, rfl⟩ := hs
    exact (hg u).1

end GlobalTheory
