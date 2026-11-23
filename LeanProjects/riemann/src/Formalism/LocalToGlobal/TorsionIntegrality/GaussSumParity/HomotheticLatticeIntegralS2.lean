import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.StatementG
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.EisensteinS2LimitFormula

noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.D

open Formalism.InvariantFactorPaths.G7 (UnrOK)
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension omegaK)

def normInt (dK : ℕ) (m n : ℤ) : ℤ := m ^ 2 + m * n + n ^ 2 * (((dK : ℤ) + 1) / 4)

def SqrtKur : Prop :=
  ∀ (dK : ℕ), Squarefree dK → dK % 4 = 3 → ∀ (l : ℕ) [Fact l.Prime], 5 ≤ l →
    (¬ ∃ a : ZMod l, a ^ 2 = -(dK : ZMod l)) → ∀ ι : ℂ ≃+* ℂ_[l],
    ι (omegaK dK) ∈ MaximalUnramifiedExtension l ∧
    ∀ σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l, UnrOK (MaximalUnramifiedExtension l) l σ → ∀ w : MaximalUnramifiedExtension l, (w : ℂ_[l]) = ι (omegaK dK) →
      σ w = 1 - w

def DenseOK : Prop :=
  ∀ (dK : ℕ), Squarefree dK → dK % 4 = 3 → ∀ (l : ℕ) [Fact l.Prime], 5 ≤ l →
    (¬ ∃ a : ZMod l, a ^ 2 = -(dK : ZMod l)) → ∀ ι : ℂ ≃+* ℂ_[l],
    ∀ σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l, UnrOK (MaximalUnramifiedExtension l) l σ → ∀ α : MaximalUnramifiedExtension l, ‖α‖ = 1 → σ (σ α) = α →
    ∀ ε : ℝ, 0 < ε → ∃ m n : ℤ, ¬ (l : ℤ) ∣ normInt dK m n ∧
      ‖ι ((m : ℂ) + (n : ℂ) * omegaK dK) - (α : ℂ_[l])‖ < ε

def HomotheticLatticeIntegralS2 : Prop :=
  Formalism.L2.Th1.CM.CM4 →
  ∀ (dK : ℕ) (L : PeriodPair), Squarefree dK → dK % 4 = 3 → Formalism.L2.Th1.CM.HasCMBy dK L →
  ∀ (l : ℕ) [Fact l.Prime], 5 ≤ l → ¬ l ∣ dK → (¬ ∃ a : ZMod l, a ^ 2 = -(dK : ZMod l)) →
  ∀ ι : ℂ ≃+* ℂ_[l], ∀ g2 g3 : ℂ_[l], Formalism.L2.Th1.CM.IsGoodModel l L ι g2 g3 →
    ∃ (c : ℂ) (hc : c ≠ 0), g2 = ι (Formalism.L2.Th1.F.scalePair L c hc).g₂ ∧
      g3 = ι (Formalism.L2.Th1.F.scalePair L c hc).g₃ ∧
      ι (Formalism.L2.Th1.F.s2 (Formalism.L2.Th1.F.scalePair L c hc)) ∈ MaximalUnramifiedExtension l ∧
      ‖ι (Formalism.L2.Th1.F.s2 (Formalism.L2.Th1.F.scalePair L c hc))‖ ≤ 1

def NRDense : Prop :=
  Formalism.L2.Th1.CM.CM4 →
  ∀ (dK : ℕ) (L : PeriodPair), Squarefree dK → dK % 4 = 3 → Formalism.L2.Th1.CM.HasCMBy dK L →
  ∀ (l : ℕ) [Fact l.Prime], 5 ≤ l → ¬ l ∣ dK → (¬ ∃ a : ZMod l, a ^ 2 = -(dK : ZMod l)) →
  ∀ ι : ℂ ≃+* ℂ_[l], ∀ g2 g3 ε s2 : MaximalUnramifiedExtension l, Formalism.L2.Th1.CM.IsGoodModel l L ι g2 g3 → ‖ε‖ = 1 →
    (∀ n, ‖PowerSeries.coeff n (thetaS l g2 g3 ε)‖ ≤ 1) →
  ∀ (c : ℂ) (hc : c ≠ 0), (g2 : ℂ_[l]) = ι (Formalism.L2.Th1.F.scalePair L c hc).g₂ →
    (g3 : ℂ_[l]) = ι (Formalism.L2.Th1.F.scalePair L c hc).g₃ →
    (s2 : ℂ_[l]) = ι (Formalism.L2.Th1.F.s2 (Formalism.L2.Th1.F.scalePair L c hc)) →
  ∀ σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l, UnrOK (MaximalUnramifiedExtension l) l σ →
  ∀ (m n : ℤ), ¬ (l : ℤ) ∣ normInt dK m n → ∀ α : MaximalUnramifiedExtension l,
    (α : ℂ_[l]) = ι ((m : ℂ) + (n : ℂ) * omegaK dK) → NormRel l σ (phFF l g2 g3 s2 ε) α

end Formalism.L2.Th1.D
