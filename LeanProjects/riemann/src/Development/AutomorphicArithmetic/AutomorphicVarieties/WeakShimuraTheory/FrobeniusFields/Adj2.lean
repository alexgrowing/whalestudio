import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FrobeniusFields.ExistsResQ
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FrobeniusFields.PrimeEq

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem int_units_mul_neg_one_eq_of_ne (u v : ℤˣ) (h : u ≠ v) : u * -1 = v := by
  rcases Int.units_eq_one_or u with rfl | rfl <;> rcases Int.units_eq_one_or v with rfl | rfl <;>
    simp_all

theorem UpperTheory.V.Ws.adj2 :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ (X : Set2 D) (g : G ℚ Ω) (s₁ s₂ s₃ : ℤˣ), ∃ g', X.φ g' = s₁ ∧ X.η g' = s₂ ∧ X.η' g' = s₃ ∧ D.Psi g' = D.Psi g ∧ D.ξ g' = D.ξ g ∧ D.om g' = D.om g ∧ X.κ g' = X.κ g := by
  intro Ω _ _ _ l _ c D hD X g s₁ s₂ s₃
  obtain ⟨huniq, -, -, -, hout⟩ := away D hD
  have hφ := X.hφ
  have hη := X.hη
  have hη' := X.hη'
  have pp₃ := hφ.prime
  have pp := hη.prime
  have pp' := hη'.prime
  have n₃ : X.p₃ ∉ D.S := hφ.nm
  have n₁ : X.p ∉ D.S := fun h => hη.nm (Finset.mem_insert_of_mem h)
  have n₂ : X.p' ∉ D.S := fun h => hη'.nm (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
  have d₃ : X.p ≠ X.p₃ := fun h => hη.nm (h ▸ Finset.mem_insert_self _ _)
  have d₃' : X.p' ≠ X.p₃ := fun h => hη'.nm (h ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  have d' : X.p' ≠ X.p := fun h => hη'.nm (h ▸ Finset.mem_insert_self _ _)
  have kill : ∀ q, Nat.Prime q → q ∉ D.S → ∀ t ∈ Ine (D.pl q),
      D.Psi t = 1 ∧ D.ξ t = 1 ∧ D.om t = 1 ∧ X.κ t = 1 := by
    intro q hq hqS t ht
    obtain ⟨haw, hk⟩ := hout (D.pl q) q hq hqS (hD.pl_over q hq)
    obtain ⟨a1, a2, a3⟩ := hk t ht
    exact ⟨a1, a2, a3, MonoidHom.mem_ker.1 (X.kap.unrS (D.pl q) haw ht)⟩
  have off : ∀ q r, Nat.Prime q → Nat.Prime r → q ≠ r → ¬ (D.pl q).valuation (r : Ω) < 1 := by
    intro q r hq hr hqr hv
    exact hqr (huniq (D.pl q) q r hq hr (hD.pl_over q hq) hv)
  obtain ⟨h₃, m₃, e₃⟩ := hφ.ram (D.pl X.p₃) (hD.pl_over _ pp₃)
  obtain ⟨h₁, m₁, e₁⟩ := hη.ram (D.pl X.p) (hD.pl_over _ pp)
  obtain ⟨h₂, m₂, e₂⟩ := hη'.ram (D.pl X.p') (hD.pl_over _ pp')
  have a₃ : X.η h₃ = 1 := MonoidHom.mem_ker.1 (hη.unr _ (off _ _ pp₃ pp d₃.symm) m₃)
  have b₃ : X.η' h₃ = 1 := MonoidHom.mem_ker.1 (hη'.unr _ (off _ _ pp₃ pp' d₃'.symm) m₃)
  have a₁ : X.φ h₁ = 1 := MonoidHom.mem_ker.1 (hφ.unr _ (off _ _ pp pp₃ d₃) m₁)
  have b₁ : X.η' h₁ = 1 := MonoidHom.mem_ker.1 (hη'.unr _ (off _ _ pp pp' d'.symm) m₁)
  have a₂ : X.φ h₂ = 1 := MonoidHom.mem_ker.1 (hφ.unr _ (off _ _ pp' pp₃ d₃') m₂)
  have b₂ : X.η h₂ = 1 := MonoidHom.mem_ker.1 (hη.unr _ (off _ _ pp' pp d') m₂)
  obtain ⟨k₃, k₃', k₃'', k₃'''⟩ := kill _ pp₃ n₃ h₃ m₃
  obtain ⟨k₁, k₁', k₁'', k₁'''⟩ := kill _ pp n₁ h₁ m₁
  obtain ⟨k₂, k₂', k₂'', k₂'''⟩ := kill _ pp' n₂ h₂ m₂
  obtain ⟨t₃, f₃, u₃, v₃, w₃, x₃, y₃, z₃⟩ : ∃ t, X.φ (g * t) = s₁ ∧ X.η t = 1 ∧ X.η' t = 1 ∧
      D.Psi t = 1 ∧ D.ξ t = 1 ∧ D.om t = 1 ∧ X.κ t = 1 := by
    by_cases hc : X.φ g = s₁
    · exact ⟨1, by simpa using hc, by simp, by simp, by simp, by simp, by simp, by simp⟩
    · exact ⟨h₃, by rw [map_mul, e₃]; exact int_units_mul_neg_one_eq_of_ne _ _ hc, a₃, b₃, k₃, k₃', k₃'', k₃'''⟩
  obtain ⟨t₁, f₁, u₁, v₁, w₁, x₁, y₁, z₁⟩ : ∃ t, X.η (g * t₃ * t) = s₂ ∧ X.φ t = 1 ∧ X.η' t = 1 ∧
      D.Psi t = 1 ∧ D.ξ t = 1 ∧ D.om t = 1 ∧ X.κ t = 1 := by
    by_cases hc : X.η (g * t₃) = s₂
    · exact ⟨1, by simpa using hc, by simp, by simp, by simp, by simp, by simp, by simp⟩
    · exact ⟨h₁, by rw [map_mul, e₁]; exact int_units_mul_neg_one_eq_of_ne _ _ hc, a₁, b₁, k₁, k₁', k₁'', k₁'''⟩
  obtain ⟨t₂, f₂, u₂, v₂, w₂, x₂, y₂, z₂⟩ : ∃ t, X.η' (g * t₃ * t₁ * t) = s₃ ∧ X.φ t = 1 ∧ X.η t = 1 ∧
      D.Psi t = 1 ∧ D.ξ t = 1 ∧ D.om t = 1 ∧ X.κ t = 1 := by
    by_cases hc : X.η' (g * t₃ * t₁) = s₃
    · exact ⟨1, by simpa using hc, by simp, by simp, by simp, by simp, by simp, by simp⟩
    · exact ⟨h₂, by rw [map_mul, e₂]; exact int_units_mul_neg_one_eq_of_ne _ _ hc, a₂, b₂, k₂, k₂', k₂'', k₂'''⟩
  refine ⟨g * t₃ * t₁ * t₂, ?_, ?_, f₂, ?_, ?_, ?_, ?_⟩
  · rw [map_mul, map_mul, f₃, u₁, u₂, mul_one, mul_one]
  · rw [map_mul, f₁, v₂, mul_one]
  · simp [map_mul, w₃, w₁, w₂]
  · simp [map_mul, x₃, x₁, x₂]
  · simp [map_mul, y₃, y₁, y₂]
  · simp [map_mul, z₃, z₁, z₂]
