import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.UniformGaussModelCondition
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.ThetaInZIsThetaLog
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.OneLetterGaussEvery

noncomputable section
open scoped BigOperators
open Finset

namespace Formalism.L2.Th1.Top

open Formalism.L2.Th1.D
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq cob UnrOK IsLawOfLog lamF InClass hhS uS sSub)
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)

def ThmSEveryInt : Prop :=
  ∀ (dK : ℕ) (L : PeriodPair), Squarefree dK → dK % 4 = 3 → Formalism.L2.Th1.CM.HasCMBy dK L →
  ∀ (l : ℕ) [Fact l.Prime], 5 ≤ l → ¬ l ∣ dK → (¬ ∃ a : ZMod l, a ^ 2 = -(dK : ZMod l)) →
  ∀ ι : ℂ ≃+* ℂ_[l], ∀ g2 g3 ε : MaximalUnramifiedExtension l, Formalism.L2.Th1.CM.IsGoodModel l L ι g2 g3 → ‖ε‖ = 1 →
    (∀ n, ‖PowerSeries.coeff n (thetaS l g2 g3 ε)‖ ≤ 1) →
  ∃ (s2 : MaximalUnramifiedExtension l) (c : ℂ) (hc : c ≠ 0), ‖s2‖ ≤ 1 ∧
    (g2 : ℂ_[l]) = ι (Formalism.L2.Th1.F.scalePair L c hc).g₂ ∧
    (g3 : ℂ_[l]) = ι (Formalism.L2.Th1.F.scalePair L c hc).g₃ ∧
    (s2 : ℂ_[l]) = ι (Formalism.L2.Th1.F.s2 (Formalism.L2.Th1.F.scalePair L c hc)) ∧
  ∀ σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l, UnrOK (MaximalUnramifiedExtension l) l σ →
  ∀ F : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension l), IsLawOfLog l F →
  ∀ (ν r0 r1 : ℕ) [NeZero ν],
    ∃ cS : MaximalUnramifiedExtension l, ‖cS‖ ≤ 1 ∧ σ (σ cS) = cS ∧
    ∀ (om oms : Fin ν → MaximalUnramifiedExtension l) (ϖ : ℂ_[l]) (μ : PowerSeries ℂ_[l])
      (U0 Φ : MvPowerSeries (Bool × Fin ν × Fin r0 × Fin r1) ℂ_[l]),
      ϖ ^ (l ^ 2 - 1) = (l : ℂ_[l]) → OwOK (2 * ν) σ om oms → TrDual (2 * ν) σ om oms →
      PowerSeries.constantCoeff μ = 0 →
      (PowerSeries.subst μ (lamF l ϖ) : PowerSeries ℂ_[l]) = PowerSeries.X → Integral U0 →
      MvPowerSeries.constantCoeff Φ = 0 →
      Simeq Φ (sumE (MvPowerSeries.map (MaximalUnramifiedExtension l).subtype (cob F (phFF l g2 g3 s2 ε)))) →
      InClass (l : ℂ_[l]) (hhS l (uS ((cS : MaximalUnramifiedExtension l) : ℂ_[l]) ((σ cS : MaximalUnramifiedExtension l) : ℂ_[l])))
        (MvPowerSeries.subst
          (fun x => MvPowerSeries.C ϖ * sSub (conjJ (MaximalUnramifiedExtension l).subtype σ om) (conjJ (MaximalUnramifiedExtension l).subtype σ oms) μ x)
          (mvExp (-Φ) * U0))

def ThmSEveryOrth : Prop :=
  ∀ (dK : ℕ) (L : PeriodPair), Squarefree dK → dK % 4 = 3 → Formalism.L2.Th1.CM.HasCMBy dK L →
  ∀ (l : ℕ) [Fact l.Prime], 5 ≤ l → ¬ l ∣ dK → (¬ ∃ a : ZMod l, a ^ 2 = -(dK : ZMod l)) →
  ∀ ι : ℂ ≃+* ℂ_[l], ∀ g2 g3 ε : MaximalUnramifiedExtension l, Formalism.L2.Th1.CM.IsGoodModel l L ι g2 g3 → ‖ε‖ = 1 →
    (∀ n, ‖PowerSeries.coeff n (thetaS l g2 g3 ε)‖ ≤ 1) →
  ∃ (s2 : MaximalUnramifiedExtension l) (c : ℂ) (hc : c ≠ 0), ‖s2‖ ≤ 1 ∧
    (g2 : ℂ_[l]) = ι (Formalism.L2.Th1.F.scalePair L c hc).g₂ ∧
    (g3 : ℂ_[l]) = ι (Formalism.L2.Th1.F.scalePair L c hc).g₃ ∧
    (s2 : ℂ_[l]) = ι (Formalism.L2.Th1.F.s2 (Formalism.L2.Th1.F.scalePair L c hc)) ∧
  ∀ σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l, UnrOK (MaximalUnramifiedExtension l) l σ →
  ∀ F : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension l), IsLawOfLog l F →
  ∀ (ν r0 r1 : ℕ) [NeZero ν],
    ∃ cS : MaximalUnramifiedExtension l, ‖cS‖ ≤ 1 ∧ σ (σ cS) = cS ∧
    ∀ (om oms : Fin ν → MaximalUnramifiedExtension l) (ϖ : ℂ_[l]) (μ : PowerSeries ℂ_[l]),
      ϖ ^ (l ^ 2 - 1) = (l : ℂ_[l]) → OwOK (2 * ν) σ om oms → TrDual (2 * ν) σ om oms →
      PowerSeries.constantCoeff μ = 0 →
      (PowerSeries.subst μ (lamF l ϖ) : PowerSeries ℂ_[l]) = PowerSeries.X →
    ∀ (n : Type) [Fintype n] (f f' : Fin ν × Fin r0 × Fin r1 → n → MaximalUnramifiedExtension l), IsHypPair σ f f' →
    ∀ ω₀ : ℂ, ω₀ ∈ (Formalism.L2.Th1.F.scalePair L c hc).lattice → ω₀ / 2 ∉ (Formalism.L2.Th1.F.scalePair L c hc).lattice →
    ∀ (κ : Type) [Fintype κ] (r : κ → ℂ_[l]) (s : κ → n → ℂ) (N : ℕ), (∀ k, ‖r k‖ ≤ 1) → 0 < N →
      ¬ l ∣ N → (∀ k i, (N : ℂ) * s k i ∈ (Formalism.L2.Th1.F.scalePair L c hc).lattice) →
      InClass (l : ℂ_[l]) (hhS l (uS ((cS : MaximalUnramifiedExtension l) : ℂ_[l]) ((σ cS : MaximalUnramifiedExtension l) : ℂ_[l])))
        (MvPowerSeries.subst
          (fun x => MvPowerSeries.C ϖ * sSub (conjJ (MaximalUnramifiedExtension l).subtype σ om) (conjJ (MaximalUnramifiedExtension l).subtype σ oms) μ x)
          (thetaHyp l (Formalism.L2.Th1.F.scalePair L c hc) ι (ε : ℂ_[l]) ω₀ f f' r s))

def StructureTheoremCM : Prop :=
  ∀ (dK : ℕ) (L : PeriodPair), Squarefree dK → dK % 4 = 3 → Formalism.L2.Th1.CM.HasCMBy dK L →
  ∀ (l : ℕ) [Fact l.Prime], 5 ≤ l → ¬ l ∣ dK → (¬ ∃ a : ZMod l, a ^ 2 = -(dK : ZMod l)) →
  ∀ ι : ℂ ≃+* ℂ_[l], ∀ g2 g3 ε : MaximalUnramifiedExtension l, Formalism.L2.Th1.CM.IsGoodModel l L ι g2 g3 → ‖ε‖ = 1 →
    (∀ n, ‖PowerSeries.coeff n (thetaS l g2 g3 ε)‖ ≤ 1) →
  ∃ (s2 : MaximalUnramifiedExtension l) (c : ℂ) (hc : c ≠ 0), ‖s2‖ ≤ 1 ∧
    (g2 : ℂ_[l]) = ι (Formalism.L2.Th1.F.scalePair L c hc).g₂ ∧
    (g3 : ℂ_[l]) = ι (Formalism.L2.Th1.F.scalePair L c hc).g₃ ∧
    (s2 : ℂ_[l]) = ι (Formalism.L2.Th1.F.s2 (Formalism.L2.Th1.F.scalePair L c hc)) ∧
  ∀ σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l, UnrOK (MaximalUnramifiedExtension l) l σ →
  ∀ F : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension l), IsLawOfLog l F →
  ∀ (ν r0 r1 : ℕ) [NeZero ν],
    ∃ cS : MaximalUnramifiedExtension l, ‖cS‖ ≤ 1 ∧ σ (σ cS) = cS ∧
    ∀ (om oms : Fin ν → MaximalUnramifiedExtension l) (ϖ : ℂ_[l]) (μ : PowerSeries ℂ_[l]),
      ϖ ^ (l ^ 2 - 1) = (l : ℂ_[l]) → OwOK (2 * ν) σ om oms → TrDual (2 * ν) σ om oms →
      PowerSeries.constantCoeff μ = 0 →
      (PowerSeries.subst μ (lamF l ϖ) : PowerSeries ℂ_[l]) = PowerSeries.X →
    ∀ (n : Type) [Fintype n] [DecidableEq n] (f f' : Fin ν × Fin r0 × Fin r1 → n → MaximalUnramifiedExtension l), IsHypPair σ f f' →
    ∀ (Θ : MvPowerSeries n ℂ_[l]) (γ : Matrix (Fin 4 × n) (Fin 4 × n) (MaximalUnramifiedExtension l)), IsUnitaryK σ γ →
      uniformGaussModelCondition l g2 g3 s2 ε Θ γ →
      InClass (l : ℂ_[l]) (hhS l (uS ((cS : MaximalUnramifiedExtension l) : ℂ_[l]) ((σ cS : MaximalUnramifiedExtension l) : ℂ_[l])))
        (MvPowerSeries.subst
          (fun x => MvPowerSeries.C ϖ * sSub (conjJ (MaximalUnramifiedExtension l).subtype σ om) (conjJ (MaximalUnramifiedExtension l).subtype σ oms) μ x)
          (inHyp l f f' Θ))

end Formalism.L2.Th1.Top
