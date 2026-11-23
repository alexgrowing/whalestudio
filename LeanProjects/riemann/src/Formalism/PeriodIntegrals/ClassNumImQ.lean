import Mathlib

open NumberField

namespace PI.ClassNumImQ

def kron2 (D : ℤ) : ℤ := if D % 2 = 0 then 0 else if D % 8 = 1 ∨ D % 8 = 7 then 1 else -1

def kronSym (D : ℤ) (n : ℕ) : ℤ :=
  jacobiSym D (n / 2 ^ n.factorization 2) * kron2 D ^ n.factorization 2

def kron (D : ℤ) (a : ℕ) : ℂ := (kronSym D a : ℂ)

def chDir (d : ℕ) : ℕ → ℂ := kron (-(d : ℤ))

def Induces {N : ℕ} (χ : DirichletCharacter ℂ N) (f : ℕ → ℂ) (M : ℕ) : Prop :=
  χ.IsPrimitive ∧ ∀ a : ℕ, a.Coprime M → χ (a : ZMod N) = f a

def QuadData (d : ℕ) (K : Type) [Field K] [NumberField K] (b : K) : Prop :=
  d.Prime ∧ d % 4 = 3 ∧ 3 < d ∧ b ^ 2 = -(d : K) ∧ IntermediateField.adjoin ℚ {b} = ⊤

def ClassNumImQ : Prop :=
  ∀ (d : ℕ) (K : Type) [Field K] [NumberField K] (b : K), QuadData d K b →
    ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), Induces χ (chDir d) (2 * d) →
      ((classNumber K : ℕ) : ℂ) =
        ((Real.sqrt d : ℝ) : ℂ) * DirichletCharacter.LFunction χ 1 / (Real.pi : ℂ)

def ZetaFactor : Prop :=
  ∀ (d : ℕ) (K : Type) [Field K] [NumberField K] (b : K), QuadData d K b →
    ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), Induces χ (chDir d) (2 * d) →
      ∀ s : ℂ, 1 < s.re →
        dedekindZeta K s = riemannZeta s * DirichletCharacter.LFunction χ s

def IntBasis : Prop :=
  ∀ (d : ℕ) (K : Type) [Field K] [NumberField K] (b : K), QuadData d K b →
    IsIntegral ℤ ((1 + b) / 2) ∧ ∀ x : 𝓞 K, ∃ m n : ℤ, (x : K) = m + n * ((1 + b) / 2)

def Invariants : Prop :=
  ∀ (d : ℕ) (K : Type) [Field K] [NumberField K] (b : K), QuadData d K b →
    InfinitePlace.nrRealPlaces K = 0 ∧ InfinitePlace.nrComplexPlaces K = 1 ∧
      Units.regulator K = 1 ∧ Units.torsionOrder K = 2 ∧ discr K = -(d : ℤ)

end PI.ClassNumImQ
