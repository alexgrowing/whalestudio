import Formalism.SharpRestriction.GrowthBounds.RootWeights.ExtremalProjectorOfReducibility

noncomputable section

open Finset

namespace Formalism.MainNotions.G.ExtremalProjector

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees Formalism.MainNotions.G.GLWeightTheory

section

variable {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

def pf (E : GLOps n K V) (a b : Fin n) (c T : ℕ) : Module.End K V :=
  ∑ k ∈ Finset.range (T + 1),
    ((-1 : K) ^ k / ((Nat.choose (c + k) k : ℕ) : K)) • (divPowE E b a k * divPowE E a b k)

theorem ppFac_eq (E : GLOps n K V) (mu : Fin n → ℤ) (a b : Fin n) (T : ℕ) :
    ppFac E mu a b T = pf E a b (mu a - mu b + ((b : ℤ) - (a : ℤ))).toNat T := rfl

def dualOps (E : GLOps n K V) : GLOps n K V := fun x y => - E y x

end

inductive Step (n : ℕ) : List (Fin n × Fin n) → List (Fin n × Fin n) → Prop
  | swap (l1 l2 : List (Fin n × Fin n)) (a b c d : Fin n) : a ≠ c → a ≠ d → b ≠ c → b ≠ d →
      Step n (l1 ++ (a, b) :: (c, d) :: l2) (l1 ++ (c, d) :: (a, b) :: l2)
  | braid (l1 l2 : List (Fin n × Fin n)) (a b c : Fin n) : a < b → b < c →
      Step n (l1 ++ (a, b) :: (a, c) :: (b, c) :: l2) (l1 ++ (b, c) :: (a, c) :: (a, b) :: l2)
  | braid' (l1 l2 : List (Fin n × Fin n)) (a b c : Fin n) : a < b → b < c →
      Step n (l1 ++ (b, c) :: (a, c) :: (a, b) :: l2) (l1 ++ (a, b) :: (a, c) :: (b, c) :: l2)

def RestConn : Prop :=
  ∀ (n : ℕ) (ord : List (Fin n × Fin n)), NormalOrder n ord → ∀ a b : Fin n, a.val + 1 = b.val →
    ∃ l, Relation.ReflTransGen (Step n) ord ((a, b) :: l)

def RestNil : Prop :=
  ∀ (K V : Type) [Field K] [CharZero K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] (n : ℕ)
    (E : GLOps n K V), IsGLRep E → ∀ a b : Fin n, a ≠ b → ∀ k, Module.finrank K V ≤ k → (E a b) ^ k = 0

def RestKill : Prop :=
  ∀ (K V : Type) [Field K] [CharZero K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] (n : ℕ)
    (E : GLOps n K V), IsGLRep E → ∀ a b : Fin n, a ≠ b → ∀ (ν : Fin n → ℤ) (s : ℕ), (s : ℤ) = ν a - ν b + 1 →
      ∀ T : ℕ, Module.finrank K V ≤ T → ∀ x ∈ weightSp E ν, E a b (pf E a b s T x) = 0

def RestPair : Prop :=
  ∀ (K V : Type) [Field K] [CharZero K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] (n : ℕ)
    (E : GLOps n K V), IsGLRep E → ∀ a b c : Fin n, a ≠ b → a ≠ c → b ≠ c → ∀ (ν : Fin n → ℤ) (s u : ℕ),
      (u : ℤ) - (ν a - ν c) - 1 = (s : ℤ) - (ν a - ν b) →
      ∀ T : ℕ, Module.finrank K V ≤ T → ∀ w ∈ weightSp E ν,
        E b c (pf E a b s T (pf E a c u T w)) = pf E a b s T (pf E a c u T (E b c w))

def RestPair' : Prop :=
  ∀ (K V : Type) [Field K] [CharZero K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] (n : ℕ)
    (E : GLOps n K V), IsGLRep E → ∀ a b c : Fin n, a ≠ b → a ≠ c → b ≠ c → ∀ (ν : Fin n → ℤ) (t u : ℕ),
      (u : ℤ) - (ν a - ν c) - 1 = (t : ℤ) - (ν b - ν c) →
      ∀ T : ℕ, Module.finrank K V ≤ T → ∀ w ∈ weightSp E ν,
        E a b (pf E b c t T (pf E a c u T w)) = pf E b c t T (pf E a c u T (E a b w))

def RestComm : Prop :=
  ∀ (K V : Type) [Field K] [AddCommGroup V] [Module K V] (n : ℕ)
    (E : GLOps n K V), IsGLRep E → ∀ a b c d : Fin n, a ≠ c → a ≠ d → b ≠ c → b ≠ d → ∀ s s' T : ℕ,
      Commute (pf E a b s T) (pf E c d s' T)

def YBat (sg ta : ℕ) : Prop :=
  ∀ (K V : Type) [Field K] [CharZero K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] (n : ℕ)
    (E : GLOps n K V), IsGLRep E → ∀ a b c : Fin n, a ≠ b → a ≠ c → b ≠ c → ∀ (ν : Fin n → ℤ) (s t : ℕ),
      (s : ℤ) = ν a - ν b + sg + 1 → (t : ℤ) = ν b - ν c + ta + 1 →
      ∀ T : ℕ, Module.finrank K V ≤ T → ∀ x ∈ weightSp E ν,
        pf E a b s T (pf E a c (s + t) T (pf E b c t T x)) = pf E b c t T (pf E a c (s + t) T (pf E a b s T x))

def RestYB : Prop := ∀ sg ta : ℕ, YBat sg ta

end Formalism.MainNotions.G.ExtremalProjector
