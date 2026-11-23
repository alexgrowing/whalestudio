import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.FrameWith

open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

theorem UpperTheory.V.Pa.Det.finSub :
    ∀ {A M ι : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [AddCommGroup M] [Module A M] (t : A) (Z B : Submodule A M) (f : ι → M →ₗ[A] A), Irreducible t → Z.FG → (∀ i, ∀ b ∈ B, f i b = 0) → (∀ z ∈ Z, (∀ i, f i z = 0) → ∃ s : ℕ, t ^ s • z ∈ B) → ∃ T : Finset ι, ∀ z ∈ Z, (∀ i ∈ T, f i z = 0) → ∃ s : ℕ, t ^ s • z ∈ B := by
  intro A M ι _ _ _ _ _ t Z B f ht hZ hB hZB
  classical
  obtain ⟨s, rfl⟩ := hZ
  let h : ι → (↥s → A) := fun i a => f i a.1
  obtain ⟨P, ⟨T, rfl⟩, hP⟩ := (set_has_maximal_iff_noetherian (R := A) (M := ↥s → A)).mpr
    inferInstance (Set.range fun T : Finset ι => Submodule.span A (h '' (T : Set ι))) ⟨_, ⟨∅, rfl⟩⟩
  refine ⟨T, fun z hz hzT => hZB z hz fun j => ?_⟩
  have hj : h j ∈ Submodule.span A (h '' (T : Set ι)) := by
    have hle : Submodule.span A (h '' (T : Set ι)) ≤
        Submodule.span A (h '' ((insert j T : Finset ι) : Set ι)) :=
      Submodule.span_mono (Set.image_mono (by rw [Finset.coe_insert]; exact Set.subset_insert _ _))
    have heq := (eq_or_lt_of_le hle).resolve_right (hP _ ⟨insert j T, rfl⟩)
    rw [heq]
    exact Submodule.subset_span ⟨j, by simp, rfl⟩
  obtain ⟨c, rfl⟩ := Submodule.mem_span_finset'.mp hz
  let E : (↥s → A) →ₗ[A] A := Fintype.linearCombination A c
  have hE : ∀ i, f i (∑ a : ↥s, c a • a.1) = E (h i) := by
    intro i
    simp [E, h, Fintype.linearCombination_apply, map_sum, mul_comm]
  have hker : Submodule.span A (h '' (T : Set ι)) ≤ LinearMap.ker E := by
    rw [Submodule.span_le]
    rintro _ ⟨i, hi, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker]
    rw [← hE]
    exact hzT i hi
  rw [hE]
  exact hker hj
