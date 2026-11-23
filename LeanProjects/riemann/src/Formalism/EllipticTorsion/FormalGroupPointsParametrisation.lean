import Mathlib
import Formalism.EllipticTorsion.FormalGroupPointsTorsionFree
import Formalism.EllipticTorsion.WChordSeries

open PowerSeries

universe u

noncomputable section

namespace Formalism.ELL

open Formalism.G

def evalPS {K : Type u} [NormedField K] (f : PowerSeries K) (t : K) : K :=
  ∑' n : ℕ, coeff n f * t ^ n

def evalMv2 {K : Type u} [NormedField K] (F : MvPowerSeries (Fin 2) K) (a b : K) : K :=
  ∑' d : Fin 2 →₀ ℕ, MvPowerSeries.coeff d F * a ^ (d 0) * b ^ (d 1)

def uOf {K : Type u} [Field K] {W : WeierstrassCurve K} : W.toAffine.Point → K
  | .zero => 0
  | .some x y _ => -x / y

def FormalGroupPointsParametrisation : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (W : WeierstrassCurve K) (w : PowerSeries K), IntegralModel W → WFixed W w →
    (∀ t : K, 0 < ‖t‖ → ‖t‖ < 1 →
      evalPS w t ≠ 0 ∧ W.toAffine.Nonsingular (t / evalPS w t) (-1 / evalPS w t) ∧
        1 < ‖t / evalPS w t‖ ∧ -(t / evalPS w t) / (-1 / evalPS w t) = t) ∧
    (∀ (x y : K), W.toAffine.Nonsingular x y → 1 < ‖x‖ →
      0 < ‖-x / y‖ ∧ ‖-x / y‖ < 1 ∧
        x = (-x / y) / evalPS w (-x / y) ∧ y = -1 / evalPS w (-x / y))

open Classical in

def FormalGroupPointsHomomorphism : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (W : WeierstrassCurve K) (w : PowerSeries K) (F₂ : MvPowerSeries (Fin 2) K),
    IntegralModel W → WFixed W w → IntegralMv F₂ → MvPowerSeries.constantCoeff F₂ = 0 →
    ChordAt W w (MvPowerSeries.X 0) (MvPowerSeries.X 1) F₂ →
    ∀ P Q : W.toAffine.Point, InFormalGroupPoints P → InFormalGroupPoints Q → uOf (P + Q) = evalMv2 F₂ (uOf P) (uOf Q)

end Formalism.ELL
