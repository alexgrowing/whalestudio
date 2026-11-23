import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemAdjoinOfMulEqOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUnitSigmaEqMulHilbert90InvAlg
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KappaSumZeroAndStableSumMulZeroOfNotIntegral

namespace GlobalTheory.UnitLemma.TwistUnitAny

open GlobalTheory.UnitLemma Polynomial

variable {K : UQ}

theorem stable_of_unimodular (B : InvAlg K) (hg : B.g * B.σ B.g = 1) (ε : B.A) (hε : ε = 1 ∨ ε = -1)
    (β x : B.A) (hβ : B.σ β = β * (ε * B.g)) (hx : B.σ x = x) (L : Submodule K.O B.A)
    (hU : ∀ z, z ∈ L ↔ ∀ y ∈ L, B.herm (β * x) y z ∈ (algebraMap K.O K.E).range) :
    ∀ y ∈ L, B.g * y ∈ L := by
  set R := (algebraMap K.O K.E).range with hR
  set T := Algebra.trace K.E B.A with hT
  have hεT : ∀ a, T (ε * a) ∈ R ↔ T a ∈ R := by
    intro a
    rcases hε with rfl | rfl
    · rw [one_mul]
    · rw [neg_one_mul, map_neg, neg_mem_iff]
  have hsym : ∀ a b : B.A, T (β * x * a * B.σ b) ∈ R ↔ T (β * x * (B.g * b) * B.σ a) ∈ R := by
    intro a b
    rw [← TwistUnit.trace_σ_mem B (β * x * a * B.σ b),
      show B.σ (β * x * a * B.σ b) = ε * (β * x * (B.g * b) * B.σ a) by
        rw [map_mul, map_mul, map_mul, hβ, hx, B.σ_σ]; ring, hεT]
  simp only [InvAlg.herm, ← hT, ← hR] at hU
  have h1 : ∀ y ∈ L, B.σ B.g * y ∈ L := by
    intro y hy
    rw [hU]
    intro y' hy'
    rw [hsym, show β * x * (B.g * (B.σ B.g * y)) * B.σ y' = β * x * y * B.σ y' by
      linear_combination (β * x * y * B.σ y') * hg]
    exact (hU y').1 hy' y hy
  intro y hy
  rw [hU]
  intro y' hy'
  have hb : B.σ B.g * (B.σ B.g * y') ∈ L := h1 _ (h1 y' hy')
  have := (hU _).1 hb y hy
  rw [hsym] at this
  rw [show β * x * y' * B.σ (B.g * y) = β * x * (B.g * (B.σ B.g * (B.σ B.g * y'))) * B.σ y by
    rw [map_mul]; linear_combination (-(β * x * y' * B.σ B.g * B.σ y)) * hg]
  exact this

theorem twisted_unit_eq_unit_any : ∀ (K : UQ) (B : InvAlg K), B.g * B.σ B.g = 1 → B.P.Separable →
    ∀ ε : B.A, (ε = 1 ∨ ε = -1) → ∃ β₀ : B.Aˣ, B.σ (β₀ : B.A) = β₀ * (ε * B.g) ∧
      ∀ x : B.Aˣ, B.σ (x : B.A) = x →
        {L : Submodule K.O B.A | GlobalTheory.UnitLemma.IsLat K.O K.E L ∧ ∀ z, z ∈ L ↔ ∀ y ∈ L,
          B.herm ((β₀ : B.A) * x) y z ∈ (algebraMap K.O K.E).range} = B.X x := by
  intro K B hg hs ε hε
  by_cases hi : IsIntegral K.O B.g
  · exact TwistUnit.twisted_unit_eq_unit K B hg hs hi ε hε
  have hσε : B.σ ε = ε := by rcases hε with rfl | rfl <;> simp
  have hεε : ε * ε = 1 := by rcases hε with rfl | rfl <;> simp
  have hu : (ε * B.g) * B.σ (ε * B.g) = 1 := by
    rw [map_mul, hσε]; linear_combination B.g * B.σ B.g * hεε + hg
  obtain ⟨β₀, hβ⟩ := GlobalTheory.UnitLemma.HilbertNinety.exists_unit_sigma K B (ε * B.g) hu
  refine ⟨β₀, hβ, fun x hx => ?_⟩
  ext L
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨hLat, hU⟩
    exact absurd (isIntegral_of_isLat_stable L hLat B.g
      (stable_of_unimodular B hg ε hε β₀ x hβ hx L hU)) hi
  · rintro ⟨hLat, h2, -⟩
    exact absurd (isIntegral_of_isLat_stable L hLat B.g h2) hi

end GlobalTheory.UnitLemma.TwistUnitAny
