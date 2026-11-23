import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.ToDegInjective

open IsLocalRing Filter Formalism.MainNotions.V.Pf.V2.Calc UpperTheory.V.Alg UpperTheory.V.Alg.M

theorem UpperTheory.V.Alg.M.ft_holds :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O]
      (A : Type) [CommRing A] [Algebra O A] (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜] [IsCO O (𝒜 0)] (x : A →ₐ[O] O), IsWRing 𝒜 x →
    Algebra.FiniteType (𝒜 0) A ∧ ∀ I : Ideal A, M2 𝒜 I → Algebra.FiniteType O (A ⧸ I) := by
  intro O _ _ _ _ _ A _ _ 𝒜 _ _ x hx
  classical
  obtain ⟨s, -, hs⟩ := hx.gen
  have htop : ∀ a : A, a ∈ Algebra.adjoin O ((𝒜 0 : Set A) ∪ (s : Set A)) := by
    intro a
    rw [hs]
    trivial
  refine ⟨?_, ?_⟩
  · refine ⟨⟨s, top_unique ?_⟩⟩
    intro a _
    have key : Algebra.adjoin O ((𝒜 0 : Set A) ∪ (s : Set A)) ≤
        (Algebra.adjoin (𝒜 0) (s : Set A)).restrictScalars O := by
      rw [Algebra.adjoin_le_iff]
      rintro z (hz | hz)
      · exact (Subalgebra.mem_restrictScalars O).mpr
          (Subalgebra.algebraMap_mem (Algebra.adjoin (𝒜 0) (s : Set A)) (⟨z, hz⟩ : 𝒜 0))
      · exact (Subalgebra.mem_restrictScalars O).mpr (Algebra.subset_adjoin hz)
    exact (Subalgebra.mem_restrictScalars O).mp (key (htop a))
  · intro I hI
    obtain ⟨t, ht⟩ := hI
    refine ⟨⟨t ∪ s.image (Ideal.Quotient.mkₐ O I), top_unique ?_⟩⟩
    rintro y -
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mkₐ_surjective O I y
    have hm : Ideal.Quotient.mkₐ O I a ∈
        (Algebra.adjoin O ((𝒜 0 : Set A) ∪ (s : Set A))).map (Ideal.Quotient.mkₐ O I) :=
      Subalgebra.mem_map.mpr ⟨a, htop a, rfl⟩
    rw [AlgHom.map_adjoin, Set.image_union] at hm
    refine (Algebra.adjoin_le ?_) hm
    rintro z (⟨b, hb, rfl⟩ | ⟨b, hb, rfl⟩)
    · have hz : Ideal.Quotient.mkₐ O I b ∈ Submodule.span O (t : Set (A ⧸ I)) := by
        rw [ht]
        exact Submodule.mem_map_of_mem hb
      have h2 := Algebra.span_le_adjoin O (t : Set (A ⧸ I)) hz
      refine Algebra.adjoin_mono ?_ h2
      push_cast
      exact Set.subset_union_left
    · apply Algebra.subset_adjoin
      push_cast
      exact Set.mem_union_right _ (Set.mem_image_of_mem _ hb)
