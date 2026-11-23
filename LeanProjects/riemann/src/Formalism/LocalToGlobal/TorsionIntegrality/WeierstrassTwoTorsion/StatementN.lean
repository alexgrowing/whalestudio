import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.StatementI

open PowerSeries

universe u v

noncomputable section

namespace Formalism.L2.Th1.A

def PlusZCleared : Prop :=
  ∀ (K : Type u) [Field K] [CharZero K] (W : WeierstrassCurve K) (xP yP : K),
    W.toAffine.Equation xP yP →
    derivative K (derivative K (1 + X ^ 2 * (wpReg W - C (xP + W.b₂ / 12))))
        * (1 + X ^ 2 * (wpReg W - C (xP + W.b₂ / 12)))
      - derivative K (1 + X ^ 2 * (wpReg W - C (xP + W.b₂ / 12))) ^ 2
      = (2 * wpReg W - ((xPlus W xP yP).subst (expSer W) + C (W.b₂ / 12))
          - ((xPlus W xP (W.toAffine.negY xP yP)).subst (expSer W) + C (W.b₂ / 12)))
        * (1 + X ^ 2 * (wpReg W - C (xP + W.b₂ / 12))) ^ 2

def PlusNegY : Prop :=
  ∀ (R : Type u) [CommRing R] (W : WeierstrassCurve R) (xP yP : R), W.toAffine.Equation xP yP →
    (yPlus W xP yP).subst (iSer W) = (curveS W).toAffine.negY
      (xPlus W xP (W.toAffine.negY xP yP)) (yPlus W xP (W.toAffine.negY xP yP)) ∧
    X ^ 3 * (xPlus W xP yP - xPlus W xP (W.toAffine.negY xP yP))
      = -(C (2 * yP + W.a₁ * xP + W.a₃) * (2 * yS W + C W.a₁ * X * xS W + C W.a₃ * X ^ 3)
          * tS W xP ^ 2) ∧
    coeff 1 (xPlus W xP yP) = 2 * yP + W.a₁ * xP + W.a₃

def ExpAdd : Prop :=
  ∀ (K : Type u) [Field K] [CharZero K] (W : WeierstrassCurve K),
    (expSer W).subst (U₁ + U₂ : MvPowerSeries (Fin 2) K)
      = MvPowerSeries.subst (![(expSer W).subst (U₁ : MvPowerSeries (Fin 2) K),
          (expSer W).subst (U₂ : MvPowerSeries (Fin 2) K)] : Fin 2 → MvPowerSeries (Fin 2) K) (fgl W)

def FlowUnique : Prop :=
  ∀ (R : Type u) [CommRing R] (W : WeierstrassCurve R) (x y x' y' : R⟦X⟧),
    (∀ (n : ℕ) (r : R), n ≠ 0 → (n : R) * r = 0 → r = 0) →
    IsFlow (curveS W) (D W) x y → IsFlow (curveS W) (D W) x' y' →
    constantCoeff x = constantCoeff x' → constantCoeff y = constantCoeff y' → x = x' ∧ y = y'

def ChordEquation : Prop :=
  ∀ (R : Type u) [CommRing R] (W : WeierstrassCurve R) (xP yP xQ yQ t : R),
    W.toAffine.Equation xP yP → W.toAffine.Equation xQ yQ → t * (xP - xQ) = 1 →
    W.toAffine.Equation (W.toAffine.addX xP xQ ((yP - yQ) * t))
      (W.toAffine.addY xP xQ yP ((yP - yQ) * t))

def PlusPlus : Prop :=
  ∀ (R : Type u) [CommRing R] (W : WeierstrassCurve R) (xP yP xQ yQ t : R),
    (∀ (n : ℕ) (r : R), n ≠ 0 → (n : R) * r = 0 → r = 0) →
    W.toAffine.Equation xP yP → W.toAffine.Equation xQ yQ → t * (xP - xQ) = 1 →
    ∀ s : R⟦X⟧, s * (xPlus W xP yP - C xQ) = 1 →
    xPlus W (W.toAffine.addX xP xQ ((yP - yQ) * t)) (W.toAffine.addY xP xQ yP ((yP - yQ) * t))
      = (curveS W).toAffine.addX (xPlus W xP yP) (C xQ) ((yPlus W xP yP - C yQ) * s) ∧
    yPlus W (W.toAffine.addX xP xQ ((yP - yQ) * t)) (W.toAffine.addY xP xQ yP ((yP - yQ) * t))
      = (curveS W).toAffine.addY (xPlus W xP yP) (C xQ) (yPlus W xP yP)
          ((yPlus W xP yP - C yQ) * s)

end Formalism.L2.Th1.A
