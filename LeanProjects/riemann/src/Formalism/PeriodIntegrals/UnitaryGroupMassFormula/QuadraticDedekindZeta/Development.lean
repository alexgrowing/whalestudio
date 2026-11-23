import Mathlib
import Formalism.PeriodIntegrals.ClassNumImQ

open NumberField

namespace PI.ClassNumImQ.ZetaNonvanishing₂

noncomputable def cnt (K : Type) [Field K] [NumberField K] (n : ℕ) : ℕ :=
  Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n}

def CharPrime : Prop :=
  ∀ (d : ℕ), d.Prime → d % 4 = 3 → 3 < d →
    ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), Induces χ (chDir d) (2 * d) →
      ∀ p : ℕ, p.Prime → χ (p : ZMod N) = chDir d p

def CntMul : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (m n : ℕ), m.Coprime n →
    cnt K (m * n) = cnt K m * cnt K n

def GenSplit : Prop :=
  ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → ∀ p : ℕ, p.Prime →
    ∀ P Q : Ideal (𝓞 K), P ≠ ⊤ → Q ≠ ⊤ → P ⊔ Q = ⊤ → P * Q = Ideal.span {(p : 𝓞 K)} →
      ∀ k : ℕ, cnt K (p ^ k) = k + 1

def GenInert : Prop :=
  ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → ∀ p : ℕ, p.Prime →
    (Ideal.span {(p : 𝓞 K)}).IsPrime →
      ∀ k : ℕ, cnt K (p ^ k) = if Even k then 1 else 0

def GenRam : Prop :=
  ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → ∀ p : ℕ, p.Prime →
    ∀ P : Ideal (𝓞 K), P ^ 2 = Ideal.span {(p : 𝓞 K)} → ∀ k : ℕ, cnt K (p ^ k) = 1

def LocSplitOdd : Prop :=
  ∀ (d : ℕ) (K : Type) [Field K] [NumberField K] (b : K), QuadData d K b →
    ∀ p : ℕ, p.Prime → p ≠ 2 → jacobiSym (-(d : ℤ)) p = 1 →
      ∃ P Q : Ideal (𝓞 K), P ≠ ⊤ ∧ Q ≠ ⊤ ∧ P ⊔ Q = ⊤ ∧ P * Q = Ideal.span {(p : 𝓞 K)}

def LocSplitTwo : Prop :=
  ∀ (d : ℕ) (K : Type) [Field K] [NumberField K] (b : K), QuadData d K b → d % 8 = 7 →
    ∃ P Q : Ideal (𝓞 K), P ≠ ⊤ ∧ Q ≠ ⊤ ∧ P ⊔ Q = ⊤ ∧ P * Q = Ideal.span {((2 : ℕ) : 𝓞 K)}

def LocInertTwo : Prop :=
  ∀ (d : ℕ) (K : Type) [Field K] [NumberField K] (b : K), QuadData d K b → d % 8 = 3 →
    (Ideal.span {((2 : ℕ) : 𝓞 K)}).IsPrime

def LocRam : Prop :=
  ∀ (d : ℕ) (K : Type) [Field K] [NumberField K] (b : K), QuadData d K b →
    ∃ P : Ideal (𝓞 K), P ^ 2 = Ideal.span {(d : 𝓞 K)}

def CntPrimePow : Prop :=
  ∀ (d : ℕ) (K : Type) [Field K] [NumberField K] (b : K), QuadData d K b →
    ∀ p : ℕ, p.Prime → ∀ k : ℕ,
      (cnt K (p ^ k) : ℂ) = ∑ j ∈ Finset.range (k + 1), chDir d p ^ j

def CoefId : Prop :=
  ∀ (d : ℕ) (K : Type) [Field K] [NumberField K] (b : K), QuadData d K b →
    ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), Induces χ (chDir d) (2 * d) →
      ∀ n : ℕ, n ≠ 0 → (cnt K n : ℂ) = ∑ m ∈ n.divisors, χ (m : ZMod N)

def LSer : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N),
    (∀ n : ℕ, n ≠ 0 → (cnt K n : ℂ) = ∑ m ∈ n.divisors, χ (m : ZMod N)) →
      ∀ s : ℂ, 1 < s.re → dedekindZeta K s = riemannZeta s * DirichletCharacter.LFunction χ s

end PI.ClassNumImQ.ZetaNonvanishing₂
