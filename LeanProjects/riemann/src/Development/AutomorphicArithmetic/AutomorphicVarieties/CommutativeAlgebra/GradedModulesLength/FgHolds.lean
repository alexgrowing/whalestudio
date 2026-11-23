import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.ToDegInjective

open IsLocalRing Filter Formalism.MainNotions.V.Pf.V2.Calc UpperTheory.V.Alg UpperTheory.V.Alg.M

theorem UpperTheory.V.Alg.M.fg_holds :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O]
      (A : Type) [CommRing A] [Algebra O A] (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜] [IsCO O (𝒜 0)] (x : A →ₐ[O] O), IsWRing 𝒜 x →
    ∀ j, (oz 𝒜 j).FG := by
  classical
  intro O _ _ _ _ _ A _ _ 𝒜 _ _ x hx j
  obtain ⟨s, -, hadj⟩ := hx.gen
  have hadj' : Algebra.adjoin (𝒜 0) (s : Set A) = ⊤ := by
    rw [eq_top_iff]
    intro y _
    have hy : y ∈ Algebra.adjoin O ((𝒜 0 : Set A) ∪ ↑s) := by rw [hadj]; trivial
    have hle : Algebra.adjoin O ((𝒜 0 : Set A) ∪ ↑s) ≤
        (Algebra.adjoin (𝒜 0) (s : Set A)).restrictScalars O := by
      rw [Algebra.adjoin_le_iff]
      rintro z (hz | hz)
      · rw [SetLike.mem_coe, Subalgebra.mem_restrictScalars]
        exact (Algebra.adjoin (𝒜 0) (s : Set A)).algebraMap_mem ⟨z, hz⟩
      · rw [SetLike.mem_coe, Subalgebra.mem_restrictScalars]
        exact Algebra.subset_adjoin hz
    exact (Subalgebra.mem_restrictScalars O).1 (hle hy)
  haveI : Algebra.FiniteType (𝒜 0) A := ⟨⟨s, hadj'⟩⟩
  haveI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing (𝒜 0) A
  have hI : (Ideal.span (𝒜 j : Set A)).FG := IsNoetherian.noetherian _
  obtain ⟨t, ht, hspan⟩ := (Submodule.fg_span_iff_fg_span_finset_subset _).1 hI
  refine ⟨t, le_antisymm ?_ ?_⟩
  · rw [Submodule.span_le]
    exact ht
  · intro y hy
    have hyA : y ∈ 𝒜 j := hy
    have hy' : y ∈ Submodule.span A (t : Set A) := by
      rw [← hspan]
      exact Submodule.subset_span hyA
    obtain ⟨f, -, hf⟩ := Submodule.mem_span_finset.1 hy'
    have hyj : y = (DirectSum.decompose 𝒜 y j : A) := (DirectSum.decompose_of_mem_same 𝒜 hyA).symm
    rw [hyj, ← hf, DirectSum.decompose_sum, DFinsupp.finset_sum_apply, Submodule.coe_sum]
    refine Submodule.sum_mem _ fun i hi => ?_
    have e : (DirectSum.decompose 𝒜 (f i • i) j : A) = (DirectSum.decompose 𝒜 (f i) 0 : A) * i := by
      have := DirectSum.coe_decompose_mul_add_of_right_mem 𝒜 (a := f i) (i := 0) (ht hi)
      rw [zero_add] at this
      exact this
    rw [e]
    exact Submodule.smul_mem _ (DirectSum.decompose 𝒜 (f i) 0) (Submodule.subset_span hi)
