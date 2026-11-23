import Formalism.SharpRestriction.GrowthBounds.IsResidueClassZero

noncomputable section

open NumberField Formalism.FrobeniusOrbits Formalism.BasicNotions

namespace Formalism.MainNotions.G

theorem frobSet_ne' (D : D7) {p : ℕ} (hp : p.Prime) : ∃ g, g ∈ frobSet D p := by
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have : (Ideal.span {(p : ℤ)}).IsPrime := (Ideal.span_singleton_prime hpZ.ne_zero).mpr hpZ
  have : IsGalois ℚ D.host.E := D.host.hostE_isGalois
  have : IsGaloisGroup (D.host.E ≃ₐ[ℚ] D.host.E) ℤ (𝓞 D.host.E) := IsGaloisGroup.of_isFractionRing _ _ _ ℚ D.host.E
  obtain ⟨P, hP, hlo⟩ := (inferInstance : Nonempty (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 D.host.E)))
  have hne : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot (p := Ideal.span {(p : ℤ)}) (by simpa using hpZ.ne_zero) P
  have : Finite (𝓞 D.host.E ⧸ P) := Ideal.finiteQuotientOfFreeOfNeBot P hne
  obtain ⟨σ, hσ⟩ := IsArithFrobAt.exists_of_isInvariant ℤ (D.host.E ≃ₐ[ℚ] D.host.E) P
  exact ⟨_, P, hP, hlo, σ, hσ, rfl⟩

theorem hEv_of_hNeZero {D : D7} {p : ℕ} (hp : p.Prime) (hN : HNeZero D.host p) : HEv D p := by
  obtain ⟨P, hP', hL, σ, hσ, hg⟩ := Classical.epsilon_spec (frobSet_ne' D hp)
  have h1 := @hN P hP' hL σ hσ
  rw [hg] at h1
  exact h1

end Formalism.MainNotions.G

end
