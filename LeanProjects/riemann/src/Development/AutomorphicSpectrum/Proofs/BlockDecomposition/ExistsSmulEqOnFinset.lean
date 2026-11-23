import Mathlib

namespace GlobalTheory.CompanionTheory.SimpleDensity

theorem exists_smul_eq_on_finset {R ι : Type} [Ring R] [Fintype ι] (M : ι → Type)
    [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] [∀ i, IsSimpleModule R (M i)]
    (hne : ∀ i j, i ≠ j → ∀ φ : M i →ₗ[R] M j, φ = 0)
    (f : ∀ i, M i →+ M i)
    (hf : ∀ i (φ : M i →ₗ[R] M i) x, f i (φ x) = φ (f i x))
    (s : Finset (∀ i, M i)) :
    ∃ r : R, ∀ m ∈ s, ∀ i, f i (m i) = r • m i := by
  classical
  have key : ∀ (φ : Module.End R (∀ i, M i)) (m : ∀ i, M i) (i : ι),
      φ m i = ((LinearMap.proj i) ∘ₗ φ ∘ₗ LinearMap.single R M i) (m i) := by
    intro φ m i
    have hm : m = ∑ j, Pi.single j (m j) := (Finset.univ_sum_single m).symm
    conv_lhs => rw [hm]
    rw [map_sum, Finset.sum_apply, Finset.sum_eq_single i]
    · rfl
    · intro j _ hj
      have := hne j i hj ((LinearMap.proj i) ∘ₗ φ ∘ₗ LinearMap.single R M j)
      exact LinearMap.congr_fun this (m j)
    · simp
  let F : Module.End (Module.End R (∀ i, M i)) (∀ i, M i) :=
    { toFun := fun m i => f i (m i)
      map_add' := fun a b => by ext i; simp
      map_smul' := fun φ m => by
        ext i
        simp only [Module.End.smul_def, RingHom.id_apply]
        rw [key φ m i, key φ _ i, hf] }
  obtain ⟨r, hr⟩ := jacobson_density F s
  exact ⟨r, fun m hm i => congrFun (hr m hm) i⟩

theorem exists_scalar_of_simple {A N : Type} [Ring A] [Algebra ℂ A] [AddCommGroup N] [Module ℂ N] [Module A N]
    [IsScalarTower ℂ A N] [FiniteDimensional ℂ N] [IsSimpleModule A N] (φ : N →ₗ[A] N) :
    ∃ c : ℂ, ∀ x, φ x = c • x := by
  haveI : Nontrivial N := IsSimpleModule.nontrivial A N
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (φ.restrictScalars ℂ : Module.End ℂ N)
  obtain ⟨w, hw⟩ := hc.exists_hasEigenvector
  refine ⟨c, ?_⟩
  have hw1 : φ w = c • w := hw.apply_eq_smul
  let ψ : N →ₗ[A] N := φ - c • LinearMap.id
  rcases LinearMap.injective_or_eq_zero ψ with hi | h0
  · exfalso
    have hz : ψ w = 0 := by simp [ψ, hw1]
    exact hw.2 (hi (by rw [hz, map_zero]))
  · intro x
    have := LinearMap.congr_fun h0 x
    simpa [ψ, sub_eq_zero] using this

theorem exists_smul_eq_end : ∀ (A : Type) [Ring A] [Algebra ℂ A] (J : Type) [Fintype J] (M : J → Type)
    [∀ j, AddCommGroup (M j)] [∀ j, Module ℂ (M j)] [∀ j, Module A (M j)] [∀ j, IsScalarTower ℂ A (M j)]
    [∀ j, FiniteDimensional ℂ (M j)] [∀ j, IsSimpleModule A (M j)],
    (∀ i j, Nonempty (M i ≃ₗ[A] M j) → i = j) →
      ∀ f : ∀ j, Module.End ℂ (M j), ∃ a : A, ∀ j (x : M j), a • x = f j x := by
  intro A _ _ J _ M _ _ _ _ _ _ hiso f
  classical
  have hne : ∀ i j, i ≠ j → ∀ φ : M i →ₗ[A] M j, φ = 0 := by
    intro i j hij φ
    by_contra h
    exact hij (hiso i j ⟨LinearEquiv.ofBijective φ (LinearMap.bijective_of_ne_zero h)⟩)
  have hf : ∀ i (φ : M i →ₗ[A] M i) x,
      (f i).toAddMonoidHom (φ x) = φ ((f i).toAddMonoidHom x) := by
    intro i φ x
    obtain ⟨c, hc⟩ := exists_scalar_of_simple φ
    simp [hc]
  let b : ∀ j, Module.Basis (Module.Free.ChooseBasisIndex ℂ (M j)) ℂ (M j) := fun j => Module.Free.chooseBasis ℂ (M j)
  haveI : ∀ j, Fintype (Module.Free.ChooseBasisIndex ℂ (M j)) := fun j => inferInstance
  let s : Finset (∀ j, M j) :=
    Finset.univ.biUnion fun j => Finset.univ.image fun k => (Pi.single j (b j k) : ∀ j, M j)
  obtain ⟨r, hr⟩ := exists_smul_eq_on_finset M hne (fun j => (f j).toAddMonoidHom) hf s
  refine ⟨r, fun j x => ?_⟩
  have hlin : (Algebra.lsmul ℂ ℂ (M j) r : Module.End ℂ (M j)) = f j := by
    refine (b j).ext fun k => ?_
    have hm : (Pi.single j (b j k) : ∀ j, M j) ∈ s :=
      Finset.mem_biUnion.2 ⟨j, Finset.mem_univ _, Finset.mem_image.2 ⟨k, Finset.mem_univ _, rfl⟩⟩
    have := hr _ hm j
    simpa using this.symm
  exact LinearMap.congr_fun hlin x

end GlobalTheory.CompanionTheory.SimpleDensity
