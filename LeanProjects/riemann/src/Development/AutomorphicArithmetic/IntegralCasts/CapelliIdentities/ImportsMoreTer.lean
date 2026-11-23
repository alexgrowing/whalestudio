import Mathlib

theorem UpperTheory.Reformulated.B.Qf50.multiset_eq_of_sum :
    ∀ {Γ : Type} [inst : Monoid Γ] (s t : Multiset (Γ →* ℂ)),
    (∀ (g : Γ),
        (Multiset.map (fun (f : Γ →* ℂ) ↦ (f : Γ → ℂ) g) s).sum =
          (Multiset.map (fun (f : Γ →* ℂ) ↦ (f : Γ → ℂ) g) t).sum) →
      s = t := by
  classical
  intro Γ _ s t h
  have key : ∀ (u : Finset (Γ →* ℂ)) (r : Multiset (Γ →* ℂ)), r.toFinset ⊆ u → ∀ g : Γ,
      (Multiset.map (fun (f : Γ →* ℂ) ↦ (f : Γ → ℂ) g) r).sum
        = ∑ f ∈ u, (r.count f : ℂ) * f g := by
    intro u r hr g
    rw [Finset.sum_multiset_map_count, Finset.sum_subset hr]
    · exact Finset.sum_congr rfl fun f _ => by simp
    · intro f _ hf
      have : r.count f = 0 := Multiset.count_eq_zero.2 (by simpa using hf)
      simp [this]
  set u : Finset (Γ →* ℂ) := s.toFinset ∪ t.toFinset with hu
  have hs : s.toFinset ⊆ u := Finset.subset_union_left
  have ht : t.toFinset ⊆ u := Finset.subset_union_right
  have lin := linearIndependent_iff'.1 (linearIndependent_monoidHom Γ ℂ) u
    (fun f => (s.count f : ℂ) - (t.count f : ℂ)) (by
      funext g
      have e := h g
      rw [key u s hs g, key u t ht g] at e
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, sub_mul,
        Finset.sum_sub_distrib]
      exact sub_eq_zero.2 e)
  ext f
  by_cases hf : f ∈ u
  · have := lin f hf
    exact_mod_cast sub_eq_zero.1 this
  · have h1 : f ∉ s := fun m => hf (hs (by simpa using m))
    have h2 : f ∉ t := fun m => hf (ht (by simpa using m))
    rw [Multiset.count_eq_zero.2 h1, Multiset.count_eq_zero.2 h2]
