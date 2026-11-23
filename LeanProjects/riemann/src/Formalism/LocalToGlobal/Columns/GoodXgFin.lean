import Mathlib
import Formalism.LocalToGlobal.Divisibility.GoodPartHermitianSpec

open Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.L2.DIV

section Fin

variable {G : Type} [Group G] [Fintype G]

def gxIrrSet (k : Type) [Field k] : Set (G → k) :=
  {ψ | ∃ (n : ℕ) (ρ : Representation k G (Fin n → k)), ρ.IsIrreducible ∧ ρ.character = ψ}

open Classical in

theorem gx_orth {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {ψ ψ' : G → k}
    (hψ : ψ ∈ gxIrrSet (G := G) k) (hψ' : ψ' ∈ gxIrrSet (G := G) k) :
    (Nat.card G : k)⁻¹ * ∑ g : G, ψ g * ψ' g⁻¹ = if ψ = ψ' then 1 else 0 := by
  classical
  obtain ⟨n, ρ, hρ, rfl⟩ := hψ
  obtain ⟨n', ρ', hρ', rfl⟩ := hψ'
  have := hρ
  have := hρ'
  letI : Invertible (Nat.card G : k) := invertibleOfNonzero (by exact_mod_cast Nat.card_pos.ne')
  rw [Representation.char_orthonormal ρ ρ']
  by_cases h : ρ.character = ρ'.character
  · rw [if_pos h]
    have : Nonempty (ρ'.Equiv ρ) := by

      by_contra hne
      have h1 := Representation.char_orthonormal ρ ρ
      rw [if_pos ⟨Representation.Equiv.refl ρ⟩] at h1
      have h2 := Representation.char_orthonormal ρ ρ'
      rw [if_neg hne] at h2
      rw [← h] at h2
      rw [h2] at h1
      exact zero_ne_one h1
    rw [if_pos this]
  · rw [if_neg h]
    have : ¬ Nonempty (ρ'.Equiv ρ) := fun ⟨φ⟩ => h (Representation.char_iso φ).symm
    rw [if_neg this]

theorem gx_linInd {k : Type} [Field k] [IsAlgClosed k] [CharZero k] :
    LinearIndependent k (fun ψ : gxIrrSet (G := G) k => (ψ : G → k)) := by
  classical
  rw [linearIndependent_iff']
  intro s c hs ψ0 hψ0
  have key : ∀ g : G, ∑ ψ ∈ s, c ψ * (ψ : G → k) g = 0 := by
    intro g
    have := congrFun hs g
    simpa [Finset.sum_apply] using this
  have h3 : ∑ ψ ∈ s, c ψ * ((Nat.card G : k)⁻¹ * ∑ g : G, (ψ : G → k) g * (ψ0 : G → k) g⁻¹) = 0 := by
    have hre : ∑ ψ ∈ s, c ψ * ((Nat.card G : k)⁻¹ * ∑ g : G, (ψ : G → k) g * (ψ0 : G → k) g⁻¹)
        = (Nat.card G : k)⁻¹ * ∑ g : G, (∑ ψ ∈ s, c ψ * (ψ : G → k) g) * (ψ0 : G → k) g⁻¹ := by
      simp_rw [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun ψ _ => ?_
      ring
    rw [hre]
    simp [key]
  have h4 : ∀ ψ ∈ s, c ψ * ((Nat.card G : k)⁻¹ * ∑ g : G, (ψ : G → k) g * (ψ0 : G → k) g⁻¹) =
      if ψ = ψ0 then c ψ else 0 := by
    intro ψ _
    rw [gx_orth ψ.2 ψ0.2]
    by_cases h : ψ = ψ0
    · simp [h]
    · have h' : (ψ : G → k) ≠ ψ0 := fun e => h (Subtype.ext e)
      simp [h, h']
  rw [Finset.sum_congr rfl h4, Finset.sum_ite_eq' s ψ0 c] at h3
  simpa [hψ0] using h3

theorem gxIrrSet_finite {k : Type} [Field k] [IsAlgClosed k] [CharZero k] : (gxIrrSet (G := G) k).Finite := Set.finite_coe_iff.1 (gx_linInd (G := G) (k := k)).finite

theorem absIrrChar_finite {K : Type} [Field K] [CharZero K] : {χ : G → K | IsAbsIrrChar χ}.Finite := by
  haveI : CharZero (AlgebraicClosure K) :=
    charZero_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective
  apply Set.Finite.of_finite_image (f := fun χ : G → K => fun t => algebraMap K (AlgebraicClosure K) (χ t))
  · apply (gxIrrSet_finite (G := G) (k := AlgebraicClosure K)).subset
    rintro _ ⟨χ, ⟨n, ρ, hρ, hχ⟩, rfl⟩
    exact ⟨n, ρ, hρ, funext hχ⟩
  · intro a _ b _ hab
    funext t
    exact (algebraMap K (AlgebraicClosure K)).injective (congrFun hab t)

end Fin

end Formalism.L2.Col
