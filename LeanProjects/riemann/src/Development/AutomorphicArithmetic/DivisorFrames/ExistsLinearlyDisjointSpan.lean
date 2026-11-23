import Mathlib

theorem UpperTheory.exists_linearly_disjoint_span :
    ∀ (K W V : Type) [Field K] [AddCommGroup W] [Module K W] [AddCommGroup V] [Module ℂ V] (σ : K →+* ℂ) (rd : W →ₛₗ[σ] V) (C : Submodule K W) (Q : V), Q ∈ Submodule.span ℂ (rd '' (C : Set W)) → ∃ (m : ℕ) (ε : Fin m → ℂ) (g : Fin m → W), (∀ a : Fin m → K, ∑ j, σ (a j) * ε j = 0 → a = 0) ∧ (∀ j, g j ∈ C) ∧ Q = ∑ j, ε j • rd (g j) := by
  intro K W V _ _ _ _ _ σ rd C Q hQ
  letI : Algebra K ℂ := σ.toAlgebra
  obtain ⟨n, c, v, hv⟩ := Submodule.mem_span_set'.1 hQ
  choose w hwC hw using fun i => (v i).2
  let S : Submodule K ℂ := Submodule.span K (Set.range c)
  haveI : FiniteDimensional K S := FiniteDimensional.span_of_finite K (Set.finite_range c)
  let b := Module.finBasis K S
  let t : Fin n → Fin (Module.finrank K S) → K :=
    fun i j => b.repr ⟨c i, Submodule.subset_span ⟨i, rfl⟩⟩ j
  have hsm : ∀ (a : K) (z : ℂ), a • z = σ a * z := fun a z => rfl
  have hc : ∀ i, c i = ∑ j, σ (t i j) * (b j : ℂ) := by
    intro i
    have h := congrArg (fun x : S => (x : ℂ)) (b.sum_repr ⟨c i, Submodule.subset_span ⟨i, rfl⟩⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul, hsm] at h
    exact h.symm
  refine ⟨_, fun j => (b j : ℂ), fun j => ∑ i, t i j • w i, ?_, ?_, ?_⟩
  · intro a ha
    have hli := Fintype.linearIndependent_iff.1 b.linearIndependent a (by
      apply Subtype.ext
      simp only [Submodule.coe_sum, Submodule.coe_smul, hsm]
      exact ha)
    funext j
    exact hli j
  · intro j
    exact C.sum_mem fun i _ => C.smul_mem _ (hwC i)
  · rw [← hv]
    simp only [map_sum, map_smulₛₗ, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_smul, hw i, hc i]
    congr 1
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
