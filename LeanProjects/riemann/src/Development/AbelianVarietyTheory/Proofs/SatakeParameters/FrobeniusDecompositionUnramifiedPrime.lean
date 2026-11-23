import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GlobSpecOfExists
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCompleteDvrPrimitiveRoot
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.Decomp
open NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.L2.Col Formalism.BasicNotions

open scoped Pointwise

namespace GlobalTheory.UnramifiedFrobenius

theorem exists_frobenius : ∀ (E : Type) [Field E] [NumberField E] [IsGalois ℚ E] (p : ℕ), p.Prime → Algebra.IsUnramifiedIn (𝓞 E) (Ideal.span {(p : ℤ)}) → ∃ (Q : HeightOneSpectrum (𝓞 E)) (φ : E ≃ₐ[ℚ] E), ((p : ℕ) : 𝓞 E) ∈ Q.asIdeal ∧ ((p : ℕ) : 𝓞 E) ∉ Q.asIdeal ^ 2 ∧ (∀ x : 𝓞 E, φ • x - x ^ p ∈ Q.asIdeal) ∧ Nat.card (𝓞 E ⧸ Q.asIdeal) = p ^ orderOf φ ∧ (∀ g : E ≃ₐ[ℚ] E, (∀ x : 𝓞 E, g • x ∈ Q.asIdeal ↔ x ∈ Q.asIdeal) ↔ g ∈ Subgroup.zpowers φ) ∧ ∀ Q' : HeightOneSpectrum (𝓞 E), ((p : ℕ) : 𝓞 E) ∈ Q'.asIdeal → ∃ g : E ≃ₐ[ℚ] E, ∀ x : 𝓞 E, x ∈ Q'.asIdeal ↔ g • x ∈ Q.asIdeal := by
  intro E _ _ _ p hp hunr
  have : Fact p.Prime := ⟨hp⟩
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have : IsGaloisGroup (E ≃ₐ[ℚ] E) ℤ (𝓞 E) := IsGaloisGroup.of_isFractionRing _ _ _ ℚ E
  have : (Ideal.span {(p : ℤ)}).IsPrime := (Ideal.span_singleton_prime hpz.ne_zero).2 hpz
  have hover : ∀ R : HeightOneSpectrum (𝓞 E), ((p : ℕ) : 𝓞 E) ∈ R.asIdeal →
      R.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) := fun R hR =>
    (Ideal.liesOver_span_iff R.isPrime.ne_top hpz).mpr (by simpa using hR)
  obtain ⟨Q, hQ⟩ := GlobalTheory.CyclotomicCompletion.exists_place_above E hp
  have := Q.isPrime
  have hQo := hover Q hQ
  have : Finite (𝓞 E ⧸ Q.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient Q.ne_bot
  obtain ⟨φ, hφ⟩ := IsArithFrobAt.exists_of_isInvariant ℤ (E ≃ₐ[ℚ] E) Q.asIdeal
  have he : Q.asIdeal.ramificationIdx ℤ = 1 := hunr.ramificationIdx_eq_one hQo
  have hin : Nat.card (Q.asIdeal.inertia (E ≃ₐ[ℚ] E)) = 1 := by
    rw [Ideal.card_inertia_eq_ramificationIdxIn (G := E ≃ₐ[ℚ] E) (Ideal.span {(p : ℤ)}) Q.asIdeal,
      Ideal.ramificationIdxIn_eq_ramificationIdx (Ideal.span {(p : ℤ)}) Q.asIdeal (E ≃ₐ[ℚ] E), he]
  have hbot : Q.asIdeal.inertia (E ≃ₐ[ℚ] E) = ⊥ := Subgroup.eq_bot_of_card_eq _ hin
  have hstab : MulAction.stabilizer (E ≃ₐ[ℚ] E) Q.asIdeal = Subgroup.zpowers φ := by
    refine le_antisymm (fun σ hσ => ?_) (Subgroup.zpowers_le.2 hφ.mem_stabilizer)
    obtain ⟨k, ρ, hρ, rfl⟩ := Formalism.FrobeniusOrbits.Decomp.stab_eq_inertia_mul p Q.asIdeal φ σ hφ hσ
    have h1 : ρ ∈ Q.asIdeal.inertia (E ≃ₐ[ℚ] E) := hρ
    rw [hbot, Subgroup.mem_bot] at h1
    rw [h1, one_mul]
    exact Subgroup.npow_mem_zpowers φ k
  refine ⟨Q, φ, hQ, ?_, ?_, ?_, ?_, ?_⟩
  · intro h2
    have hmap : Ideal.map (algebraMap ℤ (𝓞 E)) (Ideal.span {(p : ℤ)}) =
        Ideal.span {((p : ℕ) : 𝓞 E)} := by
      rw [Ideal.map_span, Set.image_singleton, map_natCast]
    rw [← Ideal.ramificationIdx'_eq_ramificationIdx (Ideal.span {(p : ℤ)}) Q.asIdeal
      (by simpa using hp.ne_zero)] at he
    refine (Ideal.ramificationIdx'_ne_one_iff ?_).2 ?_ he
    · rw [hmap]; exact (Ideal.span_singleton_le_iff_mem _).2 hQ
    · rw [hmap]; exact (Ideal.span_singleton_le_iff_mem _).2 h2
  · intro x
    have h1 := hφ x
    rw [Formalism.TwoAdicCyclotomicDecomposition.odd_card_under p Q.asIdeal] at h1
    exact h1
  · have h1 := Ideal.card_stabilizer_eq_card_inertia_mul_finrank (G := E ≃ₐ[ℚ] E)
      (Ideal.span {(p : ℤ)}) Q.asIdeal
    rw [hin, one_mul, hstab, Nat.card_zpowers] at h1
    rw [h1, Ideal.pow_inertiaDeg p Q.asIdeal, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  · intro g
    rw [← hstab]
    exact ⟨Formalism.FrobeniusOrbits.Decomp.mem_stab_of g Q.asIdeal,
      Formalism.FrobeniusOrbits.Decomp.smul_mem_iff_of_stab g Q.asIdeal⟩
  · intro Q' hQ'
    have := Q'.isPrime
    have := hover Q' hQ'
    obtain ⟨g, hg⟩ := Ideal.exists_smul_eq_of_isGaloisGroup (Ideal.span {(p : ℤ)}) Q'.asIdeal
      Q.asIdeal (E ≃ₐ[ℚ] E)
    refine ⟨g, fun x => ?_⟩
    rw [← hg]
    exact Ideal.smul_mem_pointwise_smul_iff.symm

end GlobalTheory.UnramifiedFrobenius
