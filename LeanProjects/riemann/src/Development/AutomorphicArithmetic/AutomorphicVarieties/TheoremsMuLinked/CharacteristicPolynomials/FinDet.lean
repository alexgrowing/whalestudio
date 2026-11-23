import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.OrdZero

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.HV UpperTheory.V.Alg GlobalTheory.GalOfCusp

theorem UpperTheory.V.Th.Det.finDet :
    ∀ {K V S ι : Type} [Field K] [AddCommGroup V] [Module K V] [Module.Finite K V] (f : S → ι → V →ₗ[K] K), ∃ T : Finset S, ∀ v : V, (∀ s ∈ T, ∀ i, f s i v = 0) → ∀ s i, f s i v = 0 := by
  intro K V S ι _ _ _ _ f
  classical
  let U : Finset S → Submodule K V := fun T => ⨅ s ∈ T, ⨅ i, LinearMap.ker (f s i)
  obtain ⟨_, ⟨T, rfl⟩, hT⟩ :=
    (wellFounded_lt (α := Submodule K V)).has_min (Set.range U) ⟨U ∅, ∅, rfl⟩
  refine ⟨T, fun v hv s i => ?_⟩
  have hle : U (insert s T) ≤ U T := by
    intro w hw
    simp only [U, Submodule.mem_iInf, Finset.mem_insert] at hw ⊢
    intro t ht j
    exact hw t (Or.inr ht) j
  have heq : U (insert s T) = U T := by
    by_contra hne
    exact hT _ ⟨_, rfl⟩ (lt_of_le_of_ne hle hne)
  have hvT : v ∈ U T := by
    simp only [U, Submodule.mem_iInf, LinearMap.mem_ker]
    exact hv
  rw [← heq] at hvT
  simp only [U, Submodule.mem_iInf, LinearMap.mem_ker, Finset.mem_insert] at hvT
  exact hvT s (Or.inl rfl) i
