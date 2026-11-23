import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthShapeOne
import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.StatementN

noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.Top

open Formalism.L2.Th1.D
open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq cob UnrOK IsLawOfLog)
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)

def IsUnitaryK {K : Type} [NormedField K] (σ : K →+* K) {m : Type} [Fintype m] [DecidableEq m]
    (γ : Matrix m m K) : Prop :=
  (∀ a b, ‖γ a b‖ ≤ 1 ∧ σ (σ (γ a b)) = γ a b) ∧
  (∀ a b, ∑ k, σ (γ k a) * γ k b = if a = b then 1 else 0)

def phL (l : ℕ) [Fact l.Prime] (g2 g3 s2 ε : MaximalUnramifiedExtension l) : PowerSeries ℂ_[l] :=
  PowerSeries.map (MaximalUnramifiedExtension l).subtype (phFF l g2 g3 s2 ε)

def inHyp (l : ℕ) [Fact l.Prime] {E n : Type} [Fintype E] [Fintype n] (f f' : E → n → MaximalUnramifiedExtension l)
    (Θ : MvPowerSeries n ℂ_[l]) : MvPowerSeries (Bool × E) ℂ_[l] :=
  MvPowerSeries.subst
    (Formalism.L2.Th1.E.hypCoord (lgF ℂ_[l] l) (expF ℂ_[l] l) (MaximalUnramifiedExtension l).subtype f f') Θ

def uniformGaussModelCondition (l : ℕ) [Fact l.Prime] (g2 g3 s2 ε : MaximalUnramifiedExtension l) {n : Type} [Fintype n]
    (Θ : MvPowerSeries n ℂ_[l]) (γ : Matrix (Fin 4 × n) (Fin 4 × n) (MaximalUnramifiedExtension l)) : Prop :=
  Formalism.L2.Th1.E.ThetaFourthTensorPowerProductShape (lgF ℂ_[l] l) (expF ℂ_[l] l) (phL l g2 g3 s2 ε) (MaximalUnramifiedExtension l).subtype Θ γ

def uniformGaussModelConditionReformulated : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], 5 ≤ l →
  ∀ g2 g3 ε s2 : MaximalUnramifiedExtension l, ‖g2‖ ≤ 1 → ‖g3‖ ≤ 1 → ‖ε‖ = 1 →
    (∀ n, ‖PowerSeries.coeff n (thetaS l g2 g3 ε)‖ ≤ 1) →
  ∀ σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l, UnrOK (MaximalUnramifiedExtension l) l σ →
  ∀ F : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension l), IsLawOfLog l F →
  (∀ α : MaximalUnramifiedExtension l, ‖α‖ = 1 → σ (σ α) = α → NormRel l σ (phFF l g2 g3 s2 ε) α) →
  ∀ (n : Type) [Fintype n] [DecidableEq n] (Θ : MvPowerSeries n ℂ_[l])
    (γ : Matrix (Fin 4 × n) (Fin 4 × n) (MaximalUnramifiedExtension l)), IsUnitaryK σ γ → uniformGaussModelCondition l g2 g3 s2 ε Θ γ →
    Integral (Formalism.DworkPowerSeriesWeights.mvExp (Formalism.L2.Th1.E.phSum (phL l g2 g3 s2 ε) : MvPowerSeries n ℂ_[l]) * Θ)

def HypShape : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], 5 ≤ l →
  ∀ g2 g3 ε s2 : MaximalUnramifiedExtension l, ‖g2‖ ≤ 1 → ‖g3‖ ≤ 1 → ‖ε‖ = 1 →
    (∀ n, ‖PowerSeries.coeff n (thetaS l g2 g3 ε)‖ ≤ 1) →
  ∀ σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l, UnrOK (MaximalUnramifiedExtension l) l σ →
  ∀ F : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension l), IsLawOfLog l F →
  (∀ α : MaximalUnramifiedExtension l, ‖α‖ = 1 → σ (σ α) = α → NormRel l σ (phFF l g2 g3 s2 ε) α) →
  ∀ (N0 N1 : ℕ) (ιr : Type) [Fintype ιr] [DecidableEq ιr] (n : Type) [Fintype n]
    (f f' : ιr × Fin N0 × Fin N1 → n → MaximalUnramifiedExtension l), IsHypPair σ f f' →
  ∀ Θ : MvPowerSeries n ℂ_[l],
    Integral (Formalism.DworkPowerSeriesWeights.mvExp (Formalism.L2.Th1.E.phSum (phL l g2 g3 s2 ε) : MvPowerSeries n ℂ_[l]) * Θ) →
    ∃ U0 Φ : MvPowerSeries (Bool × ιr × Fin N0 × Fin N1) ℂ_[l], Integral U0 ∧
      MvPowerSeries.constantCoeff Φ = 0 ∧
      Simeq Φ (sumE (MvPowerSeries.map (MaximalUnramifiedExtension l).subtype (cob F (phFF l g2 g3 s2 ε)))) ∧
      inHyp l f f' Θ = Formalism.DworkPowerSeriesWeights.mvExp (-Φ) * U0

end Formalism.L2.Th1.Top
