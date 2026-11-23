import Mathlib
import Formalism.PeriodIntegrals.KoszulExact
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.KoszulExactness.Ii

universe u

namespace PI.KEX

open PI.KoszulExact

def P {R : Type u} [CommRing R] {D : ℕ} (s : Fin D → R) (i : ℕ) : Prop :=
  ∀ (j : ℕ) (x : ExteriorAlgebra R (Fin D → R)), x ∈ Li R D i ^ (j + 1) →
    dK s x = 0 → ∃ y ∈ Li R D i ^ (j + 2), dK s y = x

def F1 : Prop :=
  ∀ (R : Type u) [CommRing R] (D j : ℕ), ⋀[R]^j (Fin D → R) = Li R D D ^ j

def KoszulLowersPower : Prop :=
  ∀ (R : Type u) [CommRing R] (D : ℕ) (s : Fin D → R) (i j : ℕ)
    (x : ExteriorAlgebra R (Fin D → R)), x ∈ Li R D i ^ (j + 1) → dK s x ∈ Li R D i ^ j

def KoszulImageInIdeal : Prop :=
  ∀ (R : Type u) [CommRing R] (D : ℕ) (s : Fin D → R) (i : ℕ)
    (x : ExteriorAlgebra R (Fin D → R)), x ∈ Li R D i ^ 1 →
      ∃ r ∈ Ii s i, dK s x = algebraMap R _ r

def secondLeviFamily : Prop :=
  ∀ (R : Type u) [CommRing R] (D : ℕ) (s : Fin D → R) (i : ℕ) (r : R), r ∈ Ii s i →
      ∃ y ∈ Li R D i ^ 1, dK s y = algebraMap R _ r

def F3 : Prop :=
  ∀ (R : Type u) [CommRing R] (D : ℕ) (i : Fin D) (j : ℕ)
    (x : ExteriorAlgebra R (Fin D → R)), x ∈ Li R D ((i : ℕ) + 1) ^ (j + 1) →
      ∃ a ∈ Li R D i ^ (j + 1), ∃ b ∈ Li R D i ^ j, x = a + eb R i * b

def F4 : Prop :=
  ∀ (R : Type u) [CommRing R] (D : ℕ) (i : Fin D) (m n : ℕ)
    (u v : ExteriorAlgebra R (Fin D → R)), u ∈ Li R D i ^ m → v ∈ Li R D i ^ n →
      u + eb R i * v = 0 → v = 0

def W : Prop :=
  ∀ (R : Type u) [CommRing R] (D : ℕ) (s : Fin D → R),
    RingTheory.Sequence.IsWeaklyRegular R (List.ofFn s) →
    ∀ (i : Fin D) (r : R), s i * r ∈ Ii s i → r ∈ Ii s i

def Step : Prop :=
  ∀ (R : Type u) [CommRing R] (D : ℕ) (s : Fin D → R),
    RingTheory.Sequence.IsWeaklyRegular R (List.ofFn s) →
    ∀ i : Fin D, P s i → P s ((i : ℕ) + 1)

def Sec : Prop :=
  ∀ (R : Type u) [CommRing R] (D : ℕ) (s : Fin D → R) (r : R),
    (∃ y ∈ ⋀[R]^1 (Fin D → R), dK s y = algebraMap R _ r) ↔ r ∈ Ideal.span (Set.range s)

end PI.KEX
