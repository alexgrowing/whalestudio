import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IsCplAtSelf
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaCplMap

open IsLocalRing UpperTheory.V.AlgebraTools

theorem UpperTheory.V.AlgebraTools.IsCplAt.isCO :
    ∀ (R₀ R : Type) [CommRing R₀] [CommRing R] [Algebra R₀ R] (p₀ : Ideal R₀) (p : Ideal R)
      (O B : Type) [CommRing O] [IsLocalRing O] [CommRing B] [IsLocalRing B] [Algebra R₀ O] [Algebra R B]
      [Algebra O B] [Algebra R₀ B] [IsScalarTower R₀ R B] [IsScalarTower R₀ O B],
      IsCplAt R₀ p₀ O → IsCplAt R p B → p.comap (algebraMap R₀ R) = p₀ →
      (∀ x : R, ∃ a : R₀, x - algebraMap R₀ R a ∈ p) → UpperTheory.V.Alg.IsCO O B := by
  intro R₀ R _ _ _ p₀ p O B _ _ _ _ _ _ _ _ _ _ hO hB hp hsurj
  have hRB : ∀ r : R, algebraMap R B r ∈ maximalIdeal B ↔ r ∈ p := by
    intro r
    rw [← hB.comap_eq, Ideal.mem_comap]
  have h0B : ∀ c : R₀, algebraMap R₀ B c ∈ maximalIdeal B ↔ c ∈ p₀ := by
    intro c
    rw [IsScalarTower.algebraMap_apply R₀ R B, hRB, ← hp, Ideal.mem_comap]
  have hmO : Ideal.map (algebraMap O B) (maximalIdeal O) ≤ maximalIdeal B := by
    have hm := IsCplAt.map_pow_eq R₀ p₀ O hO 1
    rw [pow_one, pow_one] at hm
    rw [← hm, Ideal.map_map, ← IsScalarTower.algebraMap_eq R₀ O B, Ideal.map_le_iff_le_comap]
    intro c hc
    exact (h0B c).2 hc
  have hloc : IsLocalHom (algebraMap O B) := by
    refine ⟨fun o ho => ?_⟩
    by_contra hn
    exact (IsLocalRing.mem_maximalIdeal _).1
      (hmO (Ideal.mem_map_of_mem _ ((IsLocalRing.mem_maximalIdeal _).2 hn))) ho
  have e : ∀ c : R₀, algebraMap O B (algebraMap R₀ O c) = algebraMap R B (algebraMap R₀ R c) := by
    intro c
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  have hres : ∀ x : B, ∃ o : O, x - algebraMap O B o ∈ maximalIdeal B := by
    intro x
    obtain ⟨a, s, hs, hx⟩ := hB.dense 1 x
    rw [pow_one] at hx
    obtain ⟨s₀, hs₀⟩ := hsurj s
    obtain ⟨a₀, ha₀⟩ := hsurj a
    have h1 : algebraMap R B s - algebraMap O B (algebraMap R₀ O s₀) ∈ maximalIdeal B := by
      rw [e, ← map_sub]
      exact (hRB _).2 hs₀
    have h2 : algebraMap R B a - algebraMap O B (algebraMap R₀ O a₀) ∈ maximalIdeal B := by
      rw [e, ← map_sub]
      exact (hRB _).2 ha₀
    have hsu : IsUnit (algebraMap O B (algebraMap R₀ O s₀)) := by
      by_contra hn
      have hm : algebraMap O B (algebraMap R₀ O s₀) ∈ maximalIdeal B :=
        (IsLocalRing.mem_maximalIdeal _).2 hn
      have hsum := Ideal.add_mem _ h1 hm
      rw [sub_add_cancel] at hsum
      exact hs ((hRB s).1 hsum)
    obtain ⟨u, hu⟩ := hloc.map_nonunit _ hsu
    refine ⟨↑u⁻¹ * algebraMap R₀ O a₀, ?_⟩
    have key : algebraMap O B (algebraMap R₀ O s₀) * x - algebraMap O B (algebraMap R₀ O a₀)
        ∈ maximalIdeal B := by
      have hid : algebraMap O B (algebraMap R₀ O s₀) * x - algebraMap O B (algebraMap R₀ O a₀) =
          (algebraMap R B s * x - algebraMap R B a)
            - (algebraMap R B s - algebraMap O B (algebraMap R₀ O s₀)) * x
            + (algebraMap R B a - algebraMap O B (algebraMap R₀ O a₀)) := by ring
      rw [hid]
      exact Ideal.add_mem _ (Ideal.sub_mem _ hx (Ideal.mul_mem_right _ _ h1)) h2
    have hinv : algebraMap O B ↑u⁻¹ * algebraMap O B ↑u = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    have hid2 : x - algebraMap O B (↑u⁻¹ * algebraMap R₀ O a₀) = algebraMap O B ↑u⁻¹ *
        (algebraMap O B (algebraMap R₀ O s₀) * x - algebraMap O B (algebraMap R₀ O a₀)) := by
      rw [← hu, map_mul]
      linear_combination (-x) * hinv
    rw [hid2]
    exact Ideal.mul_mem_left _ _ key
  haveI := hB.noeth
  exact UpperTheory.V.Alg.IsCO.mk hB.complete hloc hres
