import Mathlib
import Formalism.PeriodIntegrals.SSAscent

namespace PI.SSAscent.UnitaryGroupMassFormula

open PI.SSAscent

def TrNondeg {k : Type} [Field k] {a : ℕ} (A : Subalgebra k (Matrix (Fin a) (Fin a) k)) : Prop :=
  ∀ x ∈ A, (∀ y ∈ A, Matrix.trace (x * y) = 0) → x = 0

def imAlg {Γ : Type} [Group Γ] {k : Type} [Field k] {a : ℕ} (ρ : Γ →* GL (Fin a) k) :
    Subalgebra k (Matrix (Fin a) (Fin a) k) :=
  Algebra.adjoin k (Set.range fun g => (ρ g : Matrix (Fin a) (Fin a) k))

def TraceNilStep : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (a : ℕ) (M : Matrix (Fin a) (Fin a) K),
    (∀ m : ℕ, 0 < m → Matrix.trace (M ^ m) = 0) → IsNilpotent M

def AscendStep : Prop :=
  ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (a : ℕ) (S : Set (Matrix (Fin a) (Fin a) K)),
    TrNondeg (Algebra.adjoin K S) →
      TrNondeg (Algebra.adjoin L ((algebraMap K L).mapMatrix '' S))

def DownStep : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (Γ : Type) [Group Γ] (a : ℕ) (ρ : Γ →* GL (Fin a) K),
    IsSSRep ρ → TrNondeg (imAlg ρ)

def UpStep : Prop :=
  ∀ (k : Type) [Field k] (Γ : Type) [Group Γ] (a : ℕ) (ρ : Γ →* GL (Fin a) k),
    TrNondeg (imAlg ρ) → IsSSRep ρ

end PI.SSAscent.UnitaryGroupMassFormula
