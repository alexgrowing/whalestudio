import Mathlib
import Formalism.EllipticTorsion.Statement

universe u

noncomputable section

namespace Formalism.ELL

open WeierstrassCurve

def InFormalGroupPoints {K : Type u} [NormedField K] {W : WeierstrassCurve K} : W.toAffine.Point → Prop
  | .zero => True
  | .some x _ _ => 1 < ‖x‖

open Classical in

def FormalGroupPointsSubgroup' : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] (W : WeierstrassCurve K),
    IntegralModel W → ‖W.Δ‖ = 1 →
    ∀ P Q : W.toAffine.Point, InFormalGroupPoints P → InFormalGroupPoints Q → InFormalGroupPoints (P + Q) ∧ InFormalGroupPoints (-P)

open Classical in

def FormalGroupPointsTorsionFree : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] (W : WeierstrassCurve K),
    IntegralModel W → ‖W.Δ‖ = 1 →
    ∀ (n : ℕ), ‖(n : K)‖ = 1 → ∀ P : W.toAffine.Point, InFormalGroupPoints P → n • P = 0 → P = 0

open Classical in

def TorsionIntegral : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] (W : WeierstrassCurve K),
    IntegralModel W → ‖W.Δ‖ = 1 →
    ∀ (n : ℕ), ‖(n : K)‖ = 1 → ∀ (x y : K) (h : W.toAffine.Nonsingular x y),
      n • (Affine.Point.some x y h) = 0 → ‖x‖ ≤ 1 ∧ ‖y‖ ≤ 1

end Formalism.ELL
