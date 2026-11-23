import Mathlib
import Formalism.UnipotentAdelicQuotients.CharRealisedOverRootsOfUnity

set_option autoImplicit false

namespace BrauerSchur

open scoped BigOperators

section IndFun

variable {G : Type*} [Group G] [Fintype G]

open scoped Classical in

noncomputable def indFun {R : Type*} [Field R] (H : Subgroup G) (f : H → R) (g : G) : R :=
  (Nat.card H : R)⁻¹ * ∑ x : G, if hx : x⁻¹ * g * x ∈ H then f ⟨x⁻¹ * g * x, hx⟩ else 0

end IndFun

def BrauerInduction : Prop :=
  ∀ (G : Type) [Group G] [Fintype G] (L : Type) [Field L] [IsAlgClosed L] [CharZero L] (n : ℕ)
    (ρ : Representation L G (Fin n → L)),
    ∃ (r : ℕ) (H : Fin r → Subgroup G) (ψ : (i : Fin r) → (H i →* Lˣ)) (a : Fin r → ℤ),
      ∀ g : G, ρ.character g = ∑ i, (a i : L) * indFun (H i) (fun h => ((ψ i h : Lˣ) : L)) g

def InducedCharRealised : Prop :=
  ∀ (G : Type) [Group G] [Fintype G] (K : Type) [Field K] [CharZero K] (H : Subgroup G)
    (ψ : H →* Kˣ),
    ∃ (m : ℕ) (σ : Representation K G (Fin m → K)),
      ∀ g : G, LinearMap.trace K (Fin m → K) (σ g) = indFun H (fun h => ((ψ h : Kˣ) : K)) g

def SchurIndexOne : Prop :=
  ∀ (G : Type) [Group G] [Fintype G] (K : Type) [Field K] [CharZero K] (χ : G → K),
    (∃ (n : ℕ) (ρ : Representation (AlgebraicClosure K) G (Fin n → AlgebraicClosure K)),
        ρ.IsIrreducible ∧ ∀ t, ρ.character t = algebraMap K (AlgebraicClosure K) (χ t)) →
    (∃ (r : ℕ) (m : Fin r → ℕ) (σ : (i : Fin r) → Representation K G (Fin (m i) → K)) (a : Fin r → ℤ),
        ∀ g, χ g = ∑ i, (a i : K) * LinearMap.trace K (Fin (m i) → K) (σ i g)) →
    ∃ (m : ℕ) (τ : Representation K G (Fin m → K)),
      (Nontrivial (Fin m → K) ∧ Function.Surjective τ.asAlgebraHom) ∧
        ∀ g, LinearMap.trace K (Fin m → K) (τ g) = χ g

def CharRealExp : Prop :=
  ∀ (Γ : Type) [Group Γ] [Fintype Γ] (K : Type) [Field K] [CharZero K] (z : K),
    IsPrimitiveRoot z (Monoid.exponent Γ) →
    ∀ χ : Γ → K,
      (∃ (n : ℕ) (ρ : Representation (AlgebraicClosure K) Γ (Fin n → AlgebraicClosure K)),
        ρ.IsIrreducible ∧ ∀ t, ρ.character t = algebraMap K (AlgebraicClosure K) (χ t)) →
      ∃ (m : ℕ) (τ : Representation K Γ (Fin m → K)),
        (Nontrivial (Fin m → K) ∧ Function.Surjective τ.asAlgebraHom) ∧
          ∀ g, LinearMap.trace K (Fin m → K) (τ g) = χ g

end BrauerSchur
