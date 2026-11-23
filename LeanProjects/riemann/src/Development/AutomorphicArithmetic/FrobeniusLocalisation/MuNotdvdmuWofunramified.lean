import Development.AutomorphicArithmetic.FrobeniusLocalisation.MuDefs

open UpperTheory.HF

open NumberField IntermediateField Ideal Formalism.HC Formalism.FrobeniusOrbits
open scoped Pointwise

private theorem mem_pow_of_prim {L : Type} [Field L] [NumberField L] (p : ℕ) [Fact p.Prime]
    (Q : Ideal (𝓞 L)) (hQ : Q.IsPrime) (hpQ : (p : 𝓞 L) ∈ Q) (η : L) (hη : IsPrimitiveRoot η p) :
    (p : 𝓞 L) ∈ Q ^ (p - 1) := by
  obtain ⟨u, hu⟩ := IsCyclotomicExtension.Rat.associated_zeta_sub_one_pow_prime p hη
  have hx : hη.toInteger - 1 ∈ Q := by
    apply hQ.mem_of_pow_mem (p - 1)
    have : (hη.toInteger - 1) ^ (p - 1) = (p : 𝓞 L) * ((u⁻¹ : (𝓞 L)ˣ) : 𝓞 L) := by
      rw [← hu, mul_assoc, Units.mul_inv, mul_one]
    rw [this]
    exact Q.mul_mem_right _ hpQ
  rw [← hu]
  exact (Q ^ (p - 1)).mul_mem_right _ (Ideal.pow_mem_pow hx (p - 1))

theorem UpperTheory.HF.Formalism.HC.HostAx.not_dvd_muW_of_unramified :
    ∀ {φ : Frame} (H : HostAx φ) (p : ℕ), p.Prime → p ≠ 2 → ∀ (P : Ideal (𝓞 H.E)), P.IsPrime → (p : 𝓞 H.E) ∈ P → (p : 𝓞 H.E) ∉ P ^ 2 → ¬ p ∣ H.muW := by
  intro φ H p hp hp2 P hP hpP hpP2 hdvd
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨ζ, hζ⟩ := (HostRaw.dvd_muW_iff _ hp.pos).1 hdvd
  have h := mem_pow_of_prim p P hP hpP ζ hζ
  have h2 : 2 ≤ p - 1 := by
    have := hp.two_le
    omega
  exact hpP2 (Ideal.pow_le_pow_right h2 h)
