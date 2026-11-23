import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.AlgDefs

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

theorem UpperTheory.V.Fr.alg_glue :
    ∀ {O A D : Type} [CommRing O] [CommRing A] [Algebra O A] [CommRing D] [Algebra O D] (𝔪 : Ideal D), ⨅ N : ℕ, 𝔪 ^ N = ⊥ → ∀ f : ∀ N : ℕ, A →ₐ[O] D ⧸ 𝔪 ^ (N + 1), (∀ a, ∃ d, ∀ N, Ideal.Quotient.mk (𝔪 ^ (N + 1)) d = f N a) → ∃ ξ : A →ₐ[O] D, ∀ a N, Ideal.Quotient.mk (𝔪 ^ (N + 1)) (ξ a) = f N a := by
  intro O A D _ _ _ _ _ 𝔪 hm f hf
  choose g hg using hf
  have uniq : ∀ x y : D, (∀ N : ℕ, Ideal.Quotient.mk (𝔪 ^ (N + 1)) x
      = Ideal.Quotient.mk (𝔪 ^ (N + 1)) y) → x = y := by
    intro x y h
    have hxy : x - y ∈ (⨅ N : ℕ, 𝔪 ^ N) := by
      rw [Ideal.mem_iInf]
      intro N
      exact Ideal.pow_le_pow_right (Nat.le_succ N) (Ideal.Quotient.eq.1 (h N))
    rw [hm, Ideal.mem_bot] at hxy
    exact sub_eq_zero.1 hxy
  refine ⟨{ toFun := g
            map_one' := uniq _ _ fun N => by rw [hg, map_one, map_one]
            map_mul' := fun a b => uniq _ _ fun N => by rw [hg, map_mul, map_mul, hg, hg]
            map_zero' := uniq _ _ fun N => by rw [hg, map_zero, map_zero]
            map_add' := fun a b => uniq _ _ fun N => by rw [hg, map_add, map_add, hg, hg]
            commutes' := fun r => uniq _ _ fun N => by
              rw [hg, AlgHom.commutes]; rfl }, fun a N => hg a N⟩
