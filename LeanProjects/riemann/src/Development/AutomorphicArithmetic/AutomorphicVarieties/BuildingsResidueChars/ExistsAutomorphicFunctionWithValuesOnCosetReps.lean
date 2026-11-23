import Mathlib

theorem UpperTheory.exists_automorphic_function_with_values_on_coset_reps :
    ∀ (Γ G K A M ι : Type) [Group Γ] [Group G] [Group K] [CommRing A] [AddCommGroup M] [Module A M] (gl : Γ →* G) (j : K →* G) (ρ : Representation A K M) (x : ι → G), (∀ g, ∃ γ i k, g = gl γ * x i * j k) → (∀ i i' γ k, x i' = gl γ * x i * j k → i = i') → (∀ i γ k, gl γ * x i = x i * j k → ρ k = 1) → ∀ v : ι → M, ∃ Φ : G → M, (∀ γ g, Φ (gl γ * g) = Φ g) ∧ (∀ g k, Φ (g * j k) = ρ k⁻¹ (Φ g)) ∧ ∀ i, Φ (x i) = v i := by
  intro Γ G K A M ι _ _ _ _ _ _ gl j ρ x hcov huniq hstab v
  have key : ∀ γ i k γ' i' k', gl γ * x i * j k = gl γ' * x i' * j k' →
      i = i' ∧ ρ k⁻¹ (v i) = ρ k'⁻¹ (v i') := by
    intro γ i k γ' i' k' h
    have e : x i' = gl (γ'⁻¹ * γ) * x i * j (k * k'⁻¹) := by
      calc x i' = (gl γ')⁻¹ * (gl γ' * x i' * j k') * (j k')⁻¹ := by group
        _ = (gl γ')⁻¹ * (gl γ * x i * j k) * (j k')⁻¹ := by rw [h]
        _ = gl (γ'⁻¹ * γ) * x i * j (k * k'⁻¹) := by
          simp only [map_mul, map_inv]
          group
    have hii : i = i' := huniq i i' _ _ e
    subst hii
    refine ⟨rfl, ?_⟩
    have e2 : gl (γ'⁻¹ * γ) * x i = x i * j (k' * k⁻¹) := by
      calc gl (γ'⁻¹ * γ) * x i = (gl (γ'⁻¹ * γ) * x i * j (k * k'⁻¹)) * (j (k * k'⁻¹))⁻¹ := by group
        _ = x i * j (k' * k⁻¹) := by
          rw [← e]
          simp only [map_mul, map_inv]
          group
    have hρ : ρ (k' * k⁻¹) = 1 := hstab i _ _ e2
    have : ρ k⁻¹ = ρ k'⁻¹ := by
      calc ρ k⁻¹ = ρ (k'⁻¹ * (k' * k⁻¹)) := by group
        _ = ρ k'⁻¹ * ρ (k' * k⁻¹) := map_mul _ _ _
        _ = ρ k'⁻¹ := by rw [hρ, mul_one]
    rw [this]
  choose γf iF kF hg using hcov
  refine ⟨fun g => ρ (kF g)⁻¹ (v (iF g)), ?_, ?_, ?_⟩
  · intro γ g
    have h : gl (γf (gl γ * g)) * x (iF (gl γ * g)) * j (kF (gl γ * g)) =
        gl (γ * γf g) * x (iF g) * j (kF g) := by
      rw [← hg (gl γ * g)]
      conv_lhs => rw [hg g]
      simp only [map_mul, mul_assoc]
    exact (key _ _ _ _ _ _ h).2
  · intro g k
    have h : gl (γf (g * j k)) * x (iF (g * j k)) * j (kF (g * j k)) =
        gl (γf g) * x (iF g) * j (kF g * k) := by
      rw [← hg (g * j k)]
      conv_lhs => rw [hg g]
      simp only [map_mul, mul_assoc]
    dsimp only
    rw [(key _ _ _ _ _ _ h).2, mul_inv_rev, map_mul]
    rfl
  · intro i
    have h : gl (γf (x i)) * x (iF (x i)) * j (kF (x i)) = gl 1 * x i * j 1 := by
      rw [← hg (x i), map_one, map_one, one_mul, mul_one]
    dsimp only
    rw [(key _ _ _ _ _ _ h).2, inv_one, map_one]
    rfl
