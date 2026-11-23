import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.LatticeMapsOfFunctorComparison

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.GradedWeylDivisibility MvPolynomial

def wtPQ (m P Q : ℕ) : Fin (m + 1) → ℤ := fun i => if i = 0 then (P : ℤ) else if i = Fin.last m then -(Q : ℤ) else 0

def twoLat (O : Type) {Kf : Type} [CommRing O] [Field Kf] [Algebra O Kf] (m P Q : ℕ)
    (Λ : Submodule O (Fin (m + 1) → Kf)) : Submodule O (MvPolynomial (Bool × (Fin (m + 1) × Fin (m + 1))) Kf) :=
  tensorLat O Kf fun b : Bool => H0 O m (letterWt m (if b then P else Q) b) Λ

def twoSp (Kf : Type) [Field Kf] (m P Q : ℕ) : Submodule Kf (MvPolynomial (Bool × (Fin (m + 1) × Fin (m + 1))) Kf) :=
  tensorLat Kf Kf fun b : Bool => dualWeyl Kf (m + 1) (m + 1) (nuOf (letterWt m (if b then P else Q) b))

def SingleWeightLatticeComparison : Prop :=
  ∀ (p n' : ℕ) (R : RS p n') (m : ℕ), 2 ≤ m → ∀ (a P Q : ℕ), P + Q + 1 ≤ 8 * a →
    ∃ (i : ℕ → MvPolynomial (Fin (m + 1) × Fin (m + 1)) R.Kf →ₗ[R.Kf]
        MvPolynomial (Bool × (Fin (m + 1) × Fin (m + 1))) R.Kf)
      (pr : ℕ → MvPolynomial (Bool × (Fin (m + 1) × Fin (m + 1))) R.Kf →ₗ[R.Kf]
        MvPolynomial (Fin (m + 1) × Fin (m + 1)) R.Kf),
      (∀ x ∈ twoSp R.Kf m P Q, ∑ j ∈ Finset.range (min P Q + 1), i j (pr j x) = x) ∧
      (∀ j ≤ min P Q,
        (∀ x ∈ twoSp R.Kf m P Q, pr j x ∈ dualWeyl R.Kf (m + 1) (m + 1) (nuOf (wtPQ m (P - j) (Q - j)))) ∧
        (∀ y ∈ dualWeyl R.Kf (m + 1) (m + 1) (nuOf (wtPQ m (P - j) (Q - j))), i j y ∈ twoSp R.Kf m P Q)) ∧
      ∀ Λ : Submodule R.O (Fin (m + 1) → R.Kf), IsLattice R.O Λ → ∀ j ≤ min P Q,
        (∀ x ∈ twoLat R.O m P Q Λ,
          ((p : R.Kf) ^ ⌈((m : ℝ) + 2) * lgA p a m⌉₊) • pr j x ∈ H0 R.O m (wtPQ m (P - j) (Q - j)) Λ) ∧
        (∀ y ∈ H0 R.O m (wtPQ m (P - j) (Q - j)) Λ,
          ((p : R.Kf) ^ ⌈((m : ℝ) + 2) * lgA p a m⌉₊) • i j y ∈ twoLat R.O m P Q Λ)

end Formalism.MainNotions.flipOneThree.Pf

end
