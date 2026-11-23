import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.StatementI
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.CurveHyp

open PowerSeries

noncomputable section

namespace Formalism.L2.Th1.E

section Norm

variable {K : Type} [NormedField K]

def IntS (f : K⟦X⟧) : Prop := ∀ n, ‖coeff n f‖ ≤ 1

def OneUnit (f : K⟦X⟧) : Prop := constantCoeff f = 1 ∧ IntS f

def GaussOne (f : K⟦X⟧) : Prop := IntS f ∧ ∃ n, ‖coeff n f‖ = 1

def UnitAt (k : ℕ) (f : K⟦X⟧) : Prop :=
  ∃ (a : K) (V : K⟦X⟧), ‖a‖ = 1 ∧ OneUnit V ∧ f = C a * X ^ k * V

def IntCurve (W : WeierstrassCurve K) : Prop :=
  ‖W.a₁‖ ≤ 1 ∧ ‖W.a₂‖ ≤ 1 ∧ ‖W.a₃‖ ≤ 1 ∧ ‖W.a₄‖ ≤ 1 ∧ ‖W.a₆‖ ≤ 1 ∧ ‖W.Δ‖ = 1

end Norm

section Points

variable {K : Type} [Field K] (W : WeierstrassCurve K)

def px : W.toAffine.Point → K
  | .zero => 0
  | .some x _ _ => x

def py : W.toAffine.Point → K
  | .zero => 0
  | .some _ y _ => y

def xT (P : W.toAffine.Point) : K⟦X⟧ := Formalism.L2.Th1.A.xPlus W (px W P) (py W P)

def x2 : W.toAffine.Point → K⟦X⟧
  | .zero => Formalism.L2.Th1.A.xS W
  | .some x y _ => X ^ 2 * Formalism.L2.Th1.A.xPlus W x y

def psi2 (P : W.toAffine.Point) : K := 2 * py W P + W.a₁ * px W P + W.a₃

def kapP (P : W.toAffine.Point) : K :=
  3 * px W P ^ 2 + 2 * W.a₂ * px W P + W.a₄ - W.a₁ * py W P

end Points

section Sys

variable {K : Type} [NormedField K] [DecidableEq K] (W : WeierstrassCurve K)
  {T : Type} [AddCommGroup T] (π : T →+ W.toAffine.Point)

def IntPts : Prop := ∀ t, π t ≠ 0 → ‖px W (π t)‖ ≤ 1 ∧ ‖py W (π t)‖ ≤ 1

def IsTransSys (G : T → K⟦X⟧) : Prop :=
  (∀ t, π t = 0 → ∃ ε : K, ‖ε‖ = 1 ∧ G t = C ε * X) ∧
  (∀ t, π t ≠ 0 → constantCoeff (G t) ≠ 0) ∧
  ∀ P Q, π Q ≠ 0 →
    X ^ 2 * (G (P + Q) * G (P - Q)) =
      C (constantCoeff (G Q) ^ 2) * (C (px W (π Q)) * X ^ 2 - x2 W (π P)) * G P ^ 2

end Sys

end Formalism.L2.Th1.E
