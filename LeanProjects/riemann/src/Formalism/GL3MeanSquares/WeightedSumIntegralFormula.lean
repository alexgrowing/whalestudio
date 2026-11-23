import Mathlib
import Formalism.GL3MeanSquares.SecondEstimateOfIntervalHypothesis

open Finset ArithmeticFunction Classical
open Formalism.HermitianLattices.ZeroFreeRegionGL2

noncomputable section

namespace Formalism.HermitianLattices.GL2b2

def WGIntegral : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (a w w' : ℝ), 0 < a → 0 < w → w ≤ w' →
    (w' : ℂ) * ZeroFreeRegionGL2.Gchi χ (a / w') - (w : ℂ) * ZeroFreeRegionGL2.Gchi χ (a / w) = -(∫ s in w..w', Formalism.ZeroFreeDirichlet.psiChi χ (a / s))

def WeightedSumIntegralFormula : Prop :=
  ∀ (a w w' : ℝ), 0 < a → 0 < w → w ≤ w' →
    w' * ZeroFreeRegionGL2.G1 (a / w') - w * ZeroFreeRegionGL2.G1 (a / w) = -(∫ s in w..w', (Chebyshev.psi (a / s) - a / s))

def TwInjective : Prop :=
  ∀ (t : ℕ) (θ : DirichletCharacter ℂ t) (q q' : ℕ) [Fact q.Prime] [Fact q'.Prime], t ≠ 0 → q ≠ 2 → q' ≠ 2 →
    q.Coprime t → q'.Coprime t → q ≠ q' →
    ∃ n : ℕ, ZeroFreeRegionGL2.tw θ q (n : ZMod (t * q)) ≠ ZeroFreeRegionGL2.tw θ q' (n : ZMod (t * q'))

def NegSymbolBridge : Prop :=
  ∀ q : ℕ, q % 4 = 3 → (∀ n : ℕ, Odd n → jacobiSym (-(q : ℤ)) n = jacobiSym (n : ℤ) q) ∧
    (jacobiSym 2 q = 1 ↔ q % 8 = 7)

def EvenRealTwoPower : Prop :=
  ∀ (e : ℕ) (h : 8 ∣ 2 ^ (e + 2)) (ξ : DirichletCharacter ℂ (2 ^ (e + 2))), ξ.Even → ξ ^ 2 = 1 →
    ξ = 1 ∨ ξ = DirichletCharacter.changeLevel h ZeroFreeRegionGL2.chi8

def NoRealZeroSmall : Prop :=
  (∀ σ : ℝ, 0 < σ → σ < 1 → riemannZeta (σ : ℂ) ≠ 0) ∧
  (∀ σ : ℝ, 0 < σ → σ < 1 → DirichletCharacter.LFunction ZeroFreeRegionGL2.chi8 (σ : ℂ) ≠ 0)

def NoExcOfNoRealZero : Prop :=
  ∀ (c₁ : ℝ) (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), c₁ / Real.log (2 * q) < 1 →
    (∀ σ : ℝ, 0 < σ → σ < 1 → DirichletCharacter.LFunction χ (σ : ℂ) ≠ 0) →
    (∀ s : ℂ, Formalism.ZeroFreeDirichlet.InRegion c₁ q s → Formalism.ZeroFreeDirichlet.IsLZero χ s → s.im = 0) →
    Formalism.ZeroFreeDirichlet.ExcZeros c₁ χ ∅

end Formalism.HermitianLattices.GL2b2
