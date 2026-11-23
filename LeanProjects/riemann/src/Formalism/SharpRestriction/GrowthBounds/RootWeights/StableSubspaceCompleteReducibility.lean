import Formalism.SharpRestriction.GrowthBounds.RootWeights.InvariantDenominatorEllPBound

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

def SatisfiesGLRelations {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V] (E : GLOps n K V) : Prop :=
  ∀ a b c d, E a b * E c d - E c d * E a b = (if b = c then E a d else 0) - (if d = a then E c b else 0)

def IsStableUnderOperators {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V] (E : GLOps n K V)
    (W : Submodule K V) : Prop := ∀ a b, ∀ x ∈ W, E a b x ∈ W

def isotypicPartIn {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V] (E : GLOps n K V)
    (W : Submodule K V) (mu : Fin n → ℤ) : Submodule K V :=
  Submodule.span K {x | ∃ u ∈ Umon E, ∃ v ∈ W, IsHWV E mu v ∧ x = u v}

def StableSubspaceCompleteReducibility : Prop :=
  ∀ (K V : Type) [Field K] [CharZero K] [AddCommGroup V] [Module K V] (n : ℕ) (E : GLOps n K V), SatisfiesGLRelations E →
    ∀ W : Submodule K V, FiniteDimensional K W → IsStableUnderOperators E W → W ≤ ⨆ mu, weightSp E mu →
      W ≤ ⨆ mu, isotypicPartIn E W mu

def HighestWeightModuleWeightBounds : Prop :=
  ∀ (K V : Type) [Field K] [CharZero K] [AddCommGroup V] [Module K V] (n : ℕ) [NeZero n] (E : GLOps n K V),
    SatisfiesGLRelations E → ∀ (mu : Fin n → ℤ) (v : V), IsHWV E mu v → ∀ u ∈ Umon E,
      u v ∈ ⨆ ν ∈ {ν : Fin n → ℤ | mu (lastIdx n) ≤ ν (lastIdx n) ∧ ν 0 ≤ mu 0}, weightSp E ν

def PolynomialOperatorsGLRelations : Prop :=
  ∀ (R : Type) [Field R] (ι : Type) [Fintype ι] (LL : Letters ι) (n : ℕ) (S : Set ι), SatisfiesGLRelations (glOps R n LL S)

def MonomialsAreWeightVectors : Prop :=
  ∀ (R : Type) [Field R] [CharZero R] (ι : Type) [Fintype ι] (LL : Letters ι) (n : ℕ) (S : Set ι),
    (∀ (m : ι × Fin n →₀ ℕ) (c : R), monomial m c ∈ weightSp (glOps R n LL S) (wtS LL S m)) ∧
    (∀ (ν : Fin n → ℤ) (x : MvPolynomial (ι × Fin n) R), x ∈ weightSp (glOps R n LL S) ν →
      ∀ m ∈ x.support, wtS LL S m = ν)

def PolynomialLocallyFinite : Prop :=
  ∀ (R : Type) [Field R] (ι : Type) [Fintype ι] (LL : Letters ι) (n : ℕ) (S : Set ι)
    (x : MvPolynomial (ι × Fin n) R), ∃ T : Submodule R (MvPolynomial (ι × Fin n) R),
      FiniteDimensional R T ∧ x ∈ T ∧ IsStableUnderOperators (glOps R n LL S) T

def DividedPowerFormulaCharZero : Prop :=
  ∀ (R : Type) [Field R] [CharZero R] (ι : Type) [Fintype ι] (LL : Letters ι) (n : ℕ) (S : Set ι)
    (a b : Fin n) (k : ℕ), a ≠ b → divPowE (glOps R n LL S) a b k = divPow R LL S a b k

def BinomialFormulaCharZero : Prop :=
  ∀ (R : Type) [Field R] [CharZero R] (ι : Type) [Fintype ι] (LL : Letters ι) (n : ℕ) (S : Set ι)
    (a : Fin n) (k : ℕ), binomE (glOps R n LL S) a k = binomPol R LL S a k

end Formalism.MainNotions.G.GLWeightTheory
