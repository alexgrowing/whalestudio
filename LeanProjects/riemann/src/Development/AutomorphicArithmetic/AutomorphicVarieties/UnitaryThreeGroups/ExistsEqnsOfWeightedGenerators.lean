import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.MopBase
open Matrix IsLocalRing UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.U3.Mop

theorem UpperTheory.exists_eqns_of_weighted_generators :
    ∀ {O A : Type} [CommRing O] [CommRing A] [Algebra O A] (𝒜 : ℤ → Submodule O A) (x : A →ₐ[O] O) (r s r' s' m : ℕ) {κ : Type} [Finite κ] (g : κ → A) (w : κ → ℤ),
          (∀ i, g i ∈ 𝒜 (w i)) → (∀ i, x (g i) = 0) → (∀ i, -2 ≤ w i ∧ w i ≤ 2) →
          Nat.card {i // w i = -1} = r + 1 → Nat.card {i // w i = -2} = s → Nat.card {i // w i = 1} = r' → Nat.card {i // w i = 2} = s' → Nat.card {i // w i = 0} = m →
          ∃ Q : Eqns 𝒜 x r s r' s' m, Q.ideal = Ideal.span (Set.range g) := by
  intro O A _ _ _ 𝒜 x r s r' s' m κ _ g w hg hx hw h1 h2 h3 h4 h5
  have key : ∀ (j : ℤ) (n : ℕ), Nat.card {i // w i = j} = n →
      ∃ F : Fin n → A, (∀ k, F k ∈ 𝒜 j ∧ x (F k) = 0) ∧ Set.range F = g '' {i | w i = j} := by
    intro j n hn
    let e := Finite.equivFinOfCardEq hn
    refine ⟨fun k => g (e.symm k).1, fun k => ⟨?_, hx _⟩, ?_⟩
    · have := hg (e.symm k).1
      rwa [(e.symm k).2] at this
    · ext a
      constructor
      · rintro ⟨k, rfl⟩
        exact ⟨(e.symm k).1, (e.symm k).2, rfl⟩
      · rintro ⟨i, hi, rfl⟩
        exact ⟨e ⟨i, hi⟩, by simp⟩
  obtain ⟨F, hF, rF⟩ := key _ _ h1
  obtain ⟨G, hG, rG⟩ := key _ _ h2
  obtain ⟨E, hE, rE⟩ := key _ _ h3
  obtain ⟨E', hE', rE'⟩ := key _ _ h4
  obtain ⟨Z, hZ, rZ⟩ := key _ _ h5
  refine ⟨⟨F, G, E, E', Z, fun i => (hF i).1, fun i => (hG i).1, fun i => (hE i).1, fun i => (hE' i).1, hZ⟩, ?_⟩
  show Ideal.span (Set.range F ∪ Set.range G ∪ Set.range E ∪ Set.range E' ∪ Set.range Z) = _
  rw [rF, rG, rE, rE', rZ, ← Set.image_union, ← Set.image_union, ← Set.image_union, ← Set.image_union,
    ← Set.image_univ]
  congr 2
  ext i
  have := hw i
  simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_univ, iff_true]
  omega
