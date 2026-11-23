import Mathlib

open Finset BigOperators

namespace GlobalTheory

theorem sum_fibre_image_eq_zero_of_integer_polarisation (D : ℕ) (E : (Fin D → Fin D) → ℝ)
    (h : ∀ n : Fin D → ℤ, ∑ a : Fin D → Fin D, (∏ j, (n (a j) : ℝ)) * E a = 0) :
    ∀ S : Finset (Fin D), ∑ a ∈ (univ : Finset (Fin D → Fin D)).filter (fun a => univ.image a = S), E a = 0 := by

  have hf : ∀ S : Finset (Fin D),
      ∑ a ∈ (univ : Finset (Fin D → Fin D)).filter (fun a => univ.image a ⊆ S), E a = 0 := by
    intro S
    have := h (fun i => if i ∈ S then 1 else 0)
    rw [← this, Finset.sum_filter]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    by_cases hs : univ.image a ⊆ S
    · have : ∀ j, a j ∈ S := fun j => hs (Finset.mem_image_of_mem a (Finset.mem_univ j))
      simp [this, hs]
    · rw [if_neg hs]
      have : ∃ j, a j ∉ S := by
        by_contra hc
        push_neg at hc
        apply hs
        intro x hx
        obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx
        exact hc j
      obtain ⟨j, hj⟩ := this
      rw [Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hj]), zero_mul]
  intro S
  induction S using Finset.strongInduction with
  | H S ih =>
    have hsplit : ∑ a ∈ (univ : Finset (Fin D → Fin D)).filter (fun a => univ.image a ⊆ S), E a
        = ∑ T ∈ S.powerset, ∑ a ∈ ((univ : Finset (Fin D → Fin D)).filter (fun a => univ.image a ⊆ S)).filter
            (fun a => univ.image a = T), E a := by
      rw [Finset.sum_fiberwise_of_maps_to]
      intro a ha
      simpa using (Finset.mem_filter.mp ha).2
    rw [hf S, ← Finset.add_sum_erase _ _ (Finset.mem_powerset_self S)] at hsplit
    have hrest : ∑ T ∈ S.powerset.erase S, ∑ a ∈ ((univ : Finset (Fin D → Fin D)).filter (fun a => univ.image a ⊆ S)).filter
            (fun a => univ.image a = T), E a = 0 := by
      refine Finset.sum_eq_zero (fun T hT => ?_)
      obtain ⟨hTS, hTsub⟩ := Finset.mem_erase.mp hT
      have hss : T ⊂ S := Finset.ssubset_iff_subset_ne.mpr ⟨Finset.mem_powerset.mp hTsub, hTS⟩
      rw [← ih T hss, Finset.filter_filter]
      refine Finset.sum_congr ?_ (fun _ _ => rfl)
      ext a
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · exact fun h => h.2
      · intro h; exact ⟨h ▸ hss.subset, h⟩
    rw [hrest, add_zero, Finset.filter_filter] at hsplit
    refine Eq.trans ?_ hsplit.symm
    refine Finset.sum_congr ?_ (fun _ _ => rfl)
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h; exact ⟨h ▸ Finset.Subset.refl _, h⟩
    · exact fun h => h.2

theorem sum_perm_eq_zero_of_polarisation :
    ∀ (D : ℕ) (E : (Fin D → Fin D) → ℝ),
      (∀ n : Fin D → ℤ, ∑ a : Fin D → Fin D, (∏ j, (n (a j) : ℝ)) * E a = 0) →
        ∑ σ : Equiv.Perm (Fin D), E σ = 0 := by
  intro D E h
  rw [← sum_fibre_image_eq_zero_of_integer_polarisation D E h univ]
  refine Finset.sum_bij (fun σ _ => (σ : Fin D → Fin D)) ?_ ?_ ?_ ?_
  · intro σ _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    ext x
    simp only [Finset.mem_image, Finset.mem_univ, true_and, iff_true]
    exact ⟨σ.symm x, by simp⟩
  · intro σ _ τ _ hst
    exact Equiv.ext (fun x => congrFun hst x)
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
    have hs : Function.Surjective a := by
      intro x
      have : x ∈ univ.image a := by rw [ha]; exact Finset.mem_univ x
      obtain ⟨j, _, hj⟩ := Finset.mem_image.mp this
      exact ⟨j, hj⟩
    have hb : Function.Bijective a := ⟨Finite.injective_iff_surjective.mpr hs, hs⟩
    exact ⟨Equiv.ofBijective a hb, Finset.mem_univ _, rfl⟩
  · intro σ _
    rfl

end GlobalTheory
