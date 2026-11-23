import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.LocStep

noncomputable section

open Matrix

namespace PositivityTheory.RgUd.T.Alg

open PositivityTheory.RgUd.T

variable (k : Type) [Field k] [CharZero k]

def JC : Prop :=
  ∀ (n : ℕ) (x : Matrix (Fin n) (Fin n) k), ∃ s ∈ Algebra.adjoin k {x},
    Module.End.IsSemisimple (Matrix.toLin' s) ∧ IsNilpotent (x - s)

def TrNil : Prop :=
  ∀ (n : ℕ) (x s z : Matrix (Fin n) (Fin n) k), s ∈ Algebra.adjoin k {x} → IsNilpotent (x - s) → Commute z x →
    ∀ j : ℕ, trace (z * x ^ j) = trace (z * s ^ j)

def TrAll : Prop :=
  ∀ (n : ℕ) (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (x x' : Matrix (Fin n) (Fin n) k), pZ Z x = pZ Z x' →
    ∀ z ∈ Z, ∀ j : ℕ, trace (z * x ^ j) = trace (z * x' ^ j)

def IsoOfTrace : Prop :=
  ∀ (n : ℕ) (R : Type) [CommRing R] [Algebra k R] [FiniteDimensional k R] [IsReduced R]
    (ρ ρ' : R →ₐ[k] Module.End k (Fin n → k)), (∀ r, LinearMap.trace k _ (ρ r) = LinearMap.trace k _ (ρ' r)) →
    ∃ φ : (Fin n → k) ≃ₗ[k] (Fin n → k), ∀ r v, φ (ρ r v) = ρ' r (φ v)

def Conj : Prop :=
  ∀ (n : ℕ) (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)), CR Z → ∀ s s' : Matrix (Fin n) (Fin n) k, s ∈ Bz Z → s' ∈ Bz Z →
    Module.End.IsSemisimple (Matrix.toLin' s) → Module.End.IsSemisimple (Matrix.toLin' s') →
    (∀ z ∈ Z, ∀ j : ℕ, trace (z * s ^ j) = trace (z * s' ^ j)) →
    ∃ g ∈ Gz Z, g.val * s * g⁻¹.val = s'

end PositivityTheory.RgUd.T.Alg
