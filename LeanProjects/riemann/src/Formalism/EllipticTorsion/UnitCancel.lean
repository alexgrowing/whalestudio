import Mathlib
import Formalism.EllipticTorsion.Statement

open PowerSeries

universe u

noncomputable section

namespace Formalism.ELL

open Formalism.G

def LogWeight : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CharZero K] (p q : ℕ), p.Prime →
    0 < ‖(p : K)‖ → ‖(p : K)‖ < 1 → 2 ≤ q →
    ∀ (F : FormalGroup (unitBall K)) (e l : PowerSeries K),
      IsHom (F.map (unitBall K).subtype) (F.map (unitBall K).subtype) e → IntegralPS e →
      coeff 1 e = p → (∀ n, 2 ≤ n → n < q → coeff n e = 0) →
      IsLog (F.map (unitBall K).subtype) l →
      ∀ n : ℕ, 1 ≤ n → ‖coeff n l‖ ≤ ‖(p : K)‖ ^ (-((n : ℝ) - 1) / ((q : ℝ) - 1))

def ExpWeight : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CharZero K] (p q : ℕ), p.Prime →
    0 < ‖(p : K)‖ → ‖(p : K)‖ < 1 → 2 ≤ q →
    ∀ (F : FormalGroup (unitBall K)) (e l E : PowerSeries K),
      IsHom (F.map (unitBall K).subtype) (F.map (unitBall K).subtype) e → IntegralPS e →
      coeff 1 e = p → (∀ n, 2 ≤ n → n < q → coeff n e = 0) →
      IsLog (F.map (unitBall K).subtype) l →
      constantCoeff E = 0 → E.subst l = X → l.subst E = X →
      ∀ n : ℕ, 1 ≤ n → ‖coeff n E‖ ≤ ‖(p : K)‖ ^ (-((n : ℝ) - 1) / ((q : ℝ) - 1))

def UnitCancel : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K : Type u) [NormedField K] [IsUltrametricDist K] [CharZero K]
    [NormedAlgebra ℚ_[p] K] (σ : Type) (G : MvPowerSeries σ K) (b : ℤ_[p]), IsUnit b →
      InN (algebraMap ℚ_[p] K (b : ℚ_[p]) • G) → InN G

end Formalism.ELL
