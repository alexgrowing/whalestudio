import Mathlib
import GroundTheory.LocalFields.ArtinConductor
import GroundTheory.LocalFields.ConductorTransport

noncomputable section

namespace GroundTheory.LocalField

open ValuativeRel Module Representation

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]

theorem lowerIndex_conj (σ τ : L ≃ₐ[K] L) : lowerIndex K L (τ * σ * τ⁻¹) = lowerIndex K L σ := by
  rw [← lowerIndex_autCongr τ σ]
  congr 1

theorem artinCharacter_conj (σ τ : L ≃ₐ[K] L) :
    artinCharacter K L (τ * σ * τ⁻¹) = artinCharacter K L σ := by
  by_cases hσ : σ = 1
  · subst hσ
    simp
  · have h1 : τ * σ * τ⁻¹ ≠ 1 := by
      intro h
      apply hσ
      have := congrArg (fun x ↦ τ⁻¹ * x * τ) h
      simpa [mul_assoc] using this
    rw [artinCharacter_of_ne_one hσ, artinCharacter_of_ne_one h1, lowerIndex_conj]

section Induced

variable (M : IntermediateField K L)

variable {M} in
open Classical in

def inducedFun (ψ : (L ≃ₐ[M] L) → ℂ) (s : L ≃ₐ[K] L) : ℂ :=
  (Nat.card (L ≃ₐ[M] L) : ℂ)⁻¹ * ∑ t : L ≃ₐ[K] L, ∑ h : L ≃ₐ[M] L,
    if h.restrictScalars K = t⁻¹ * s * t then ψ h else 0

variable [IsGalois K L]

open Classical in

theorem artinCharacter_restrictScalars (h : L ≃ₐ[M] L) :
    (artinCharacter K L (h.restrictScalars K) : ℂ) =
      residueDegree K M * artinCharacter M L h +
        if h = 1 then (Nat.card (L ≃ₐ[M] L) : ℂ) * (residueDegree K M * differentExponent K M : ℕ)
        else 0 := by
  by_cases h1 : h = 1
  · subst h1
    rw [if_pos rfl, show (1 : L ≃ₐ[M] L).restrictScalars K = 1 from AlgEquiv.ext fun _ ↦ rfl,
      artinCharacter_one, artinCharacter_one, IsGalois.card_aut_eq_finrank,
      ← ramificationIndex_mul_residueDegree M L, residueDegree_tower K M L,
      differentExponent_tower K M L]
    push_cast
    ring
  · have h1' : h.restrictScalars K ≠ 1 := by
      intro h'
      apply h1
      ext x
      exact congrArg (fun σ : L ≃ₐ[K] L ↦ σ x) h'
    rw [if_neg h1, artinCharacter_of_ne_one h1', artinCharacter_of_ne_one h1,
      lowerIndex_restrictScalars, residueDegree_tower K M L]
    push_cast
    ring

theorem charArtinConductor_inducedFun (ψ : (L ≃ₐ[M] L) → ℂ) :
    charArtinConductor K L (inducedFun ψ) =
      ((residueDegree K M * differentExponent K M : ℕ) : ℂ) * ψ 1 +
        residueDegree K M * charArtinConductor M L ψ := by
  classical
  have hG : (Nat.card (L ≃ₐ[K] L) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hH : (Nat.card (L ≃ₐ[M] L) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hinner : ∀ (t : L ≃ₐ[K] L) (h : L ≃ₐ[M] L), ∑ s : L ≃ₐ[K] L,
      (if h.restrictScalars K = t⁻¹ * s * t then ψ h else 0) * (artinCharacter K L s : ℂ) =
        ψ h * artinCharacter K L (h.restrictScalars K) := by
    intro t h
    have hiff : ∀ s : L ≃ₐ[K] L,
        (h.restrictScalars K = t⁻¹ * s * t) ↔ (s = t * h.restrictScalars K * t⁻¹) := by
      intro s
      constructor
      · rintro hs
        rw [hs]
        group
      · rintro rfl
        group
    simp_rw [ite_mul, zero_mul, hiff]
    rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ _), artinCharacter_conj]
  have hpt : ∀ s : L ≃ₐ[K] L, inducedFun ψ s * (artinCharacter K L s : ℂ) =
      (Nat.card (L ≃ₐ[M] L) : ℂ)⁻¹ * ∑ t : L ≃ₐ[K] L, ∑ h : L ≃ₐ[M] L,
        (if h.restrictScalars K = t⁻¹ * s * t then ψ h else 0) * (artinCharacter K L s : ℂ) := by
    intro s
    rw [inducedFun, mul_assoc, Finset.sum_mul]
    simp_rw [Finset.sum_mul]
  have hsum : ∑ s : L ≃ₐ[K] L, inducedFun ψ s * (artinCharacter K L s : ℂ) =
      (Nat.card (L ≃ₐ[M] L) : ℂ)⁻¹ * (Nat.card (L ≃ₐ[K] L) *
        ∑ h : L ≃ₐ[M] L, ψ h * artinCharacter K L (h.restrictScalars K)) := by
    rw [Finset.sum_congr rfl fun s _ ↦ hpt s, ← Finset.mul_sum, Finset.sum_comm]
    congr 1
    rw [Finset.sum_congr rfl fun t _ ↦ (Finset.sum_comm.trans
      (Finset.sum_congr rfl fun h _ ↦ hinner t h)), Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, Nat.card_eq_fintype_card]
  have hres : ∑ h : L ≃ₐ[M] L, ψ h * (artinCharacter K L (h.restrictScalars K) : ℂ) =
      residueDegree K M * ∑ h : L ≃ₐ[M] L, ψ h * artinCharacter M L h +
        ψ 1 * ((Nat.card (L ≃ₐ[M] L) : ℂ) * (residueDegree K M * differentExponent K M : ℕ)) := by
    simp_rw [artinCharacter_restrictScalars, mul_add, Finset.sum_add_distrib, mul_ite, mul_zero,
      Finset.sum_ite_eq', if_pos (Finset.mem_univ _), Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun h _ ↦ by ring
  rw [charArtinConductor, hsum, hres, charArtinConductor]
  field_simp
  ring

end Induced

end GroundTheory.LocalField
