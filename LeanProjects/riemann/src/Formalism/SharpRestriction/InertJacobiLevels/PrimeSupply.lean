import Formalism.SharpRestriction.InertJacobiLevels.SizeDataAt
import Formalism.SharpRestriction.InertJacobiLevels.GenSplit

noncomputable section

namespace Formalism.MainNotions.Inhab

open Formalism.BasicNotions Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition NumberField

def dlogQ (d : ℕ) (hd : d.Prime) : ℝ :=
  haveI : Fact d.Prime := ⟨hd⟩
  haveI : NeZero d := ⟨hd.ne_zero⟩
  (deriv (DirichletCharacter.LFunction
      ((quadraticChar (ZMod d)).ringHomComp (Int.castRingHom ℂ) : DirichletCharacter ℂ d)) 1 /
    DirichletCharacter.LFunction
      ((quadraticChar (ZMod d)).ringHomComp (Int.castRingHom ℂ) : DirichletCharacter ℂ d) 1).re

theorem dlogL_one (D : D7) : dlogL D 1 = dlogQ D.host.d D.host.hyp.2.1 := rfl

def ProgAt (C : ℝ) : Prop :=
  ∀ (M : ℕ) (a : ℤ) (X : ℝ), 0 < M → IsCoprime a (M : ℤ) → (M : ℝ) ^ C ≤ X → 3 ≤ X →
    ∃ p : ℕ, ∃ hp : p.Prime, X < p ∧ (p : ℝ) ≤ X ^ 2 ∧ (p : ℤ) ≡ a [ZMOD (M : ℤ)] ∧
      |dlogQ p hp| ≤ C * Real.log p

def ProgPrimes : Prop := ∃ C : ℝ, 1 ≤ C ∧ ProgAt C

def ProgSmall : Prop :=
  ∀ ε A : ℝ, 0 < ε → 0 < A → ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ M : ℕ, 3 ≤ M →
    Real.log M ≤ A * x ^ (ε / 5) * Real.log x ^ 2 →
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧ p ≡ 1 [MOD M] ∧ q ≡ 1 [MOD M] ∧
      Real.log p < x ^ (ε / 3) ∧ Real.log q < x ^ (ε / 3)

def ProgTwo : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ M : ℕ, 3 ≤ M → ∃ p p' : ℕ, p ≠ p' ∧ p.Prime ∧ p'.Prime ∧ p ≡ 1 [MOD M] ∧ p' ≡ 1 [MOD M] ∧
    Real.log p ≤ C * Real.log M ^ 2 ∧ Real.log p' ≤ C * Real.log M ^ 2

def RayAt (C : ℝ) : Prop :=
  ∀ (d M : ℕ) (h X : ℝ) (S : Finset ℕ), d.Prime → d % 4 = 3 → 0 < M → 0 < h → h ≤ 1 →
    C * (Real.log ((d : ℝ) * M) + Real.log (1 / h) + 1) ^ 2 ≤ Real.log X → 0 < X →
    (S.card : ℝ) ≤ X ^ ((4 : ℝ) / 5) →
    ∃ (u v : ℤ) (T : ℕ), T ∉ S ∧ T.Prime ∧ X ≤ T ∧ (T : ℝ) ≤ X * (1 + h) ∧
      (T : ℤ) = (1 + M * u) ^ 2 + d * (M * v) ^ 2

def RayWindow : Prop := ∃ C : ℝ, 1 ≤ C ∧ RayAt C

def PrimeSupply : Prop := ProgPrimes ∧ RayWindow

structure QDGood (x eps : ℝ) (q d : ℕ) : Prop where
  hyp : HostHyp q d
  q_lo : Real.exp (x ^ (eps / 5) / 2) < q
  q_hi : (q : ℝ) ≤ Real.exp (x ^ (eps / 5))
  d_lo : Real.exp (x ^ (eps / 5) * Real.log x ^ 2 / 2) < d
  d_hi : (d : ℝ) ≤ Real.exp (x ^ (eps / 5) * Real.log x ^ 2)
  split : ∀ p : ℕ, p.Prime → p ≠ 2 → (p : ℝ) ≤ x ^ (eps / 5) → jacobiSym (-(d : ℤ)) p = 1
  dlog : |dlogQ d hyp.2.1| ≤ x ^ eps

end Formalism.MainNotions.Inhab

end
