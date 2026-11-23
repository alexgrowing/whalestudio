import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.StatementG

open PowerSeries

universe u v

noncomputable section

namespace Formalism.L2.Th1.A

def divSer {R : Type u} [CommRing R] (W : WeierstrassCurve R) (n : ℤ) : R⟦X⟧ := compInv (zSer W n)

def DivSpec : Prop :=
  ∀ (R : Type u) [CommRing R] (W : WeierstrassCurve R) (n : ℤ), IsUnit (n : R) →
    constantCoeff (divSer W n) = 0 ∧ (n : R) * coeff 1 (divSer W n) = 1 ∧
    (zSer W n).subst (divSer W n) = X ∧ (divSer W n).subst (zSer W n) = X ∧
    (∀ (S : Type v) [CommRing S] (φ : R →+* S),
      PowerSeries.map φ (divSer W n) = divSer (W.map φ) n) ∧
    (n = 2 → divSer W n = halfSer W)

def DivLog : Prop :=
  ∀ (K : Type u) [Field K] [CharZero K] (W : WeierstrassCurve K) (n : ℤ), n ≠ 0 →
    C (n : K) * (logSer W).subst (divSer W n) = logSer W

def FlowDouble : Prop :=
  ∀ (A : Type u) [CommRing A] (W : WeierstrassCurve A) (D : A → A) (x y s : A),
    IsDer D → ConstCurve D W → IsFlow W D x y → s * (2 * y + W.a₁ * x + W.a₃) = 1 →
    let ℓ := (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y) * s
    W.toAffine.Equation (W.toAffine.addX x x ℓ) (W.toAffine.addY x x y ℓ) ∧
    D (W.toAffine.addX x x ℓ)
      = 2 * (2 * W.toAffine.addY x x y ℓ + W.a₁ * W.toAffine.addX x x ℓ + W.a₃) ∧
    W.toAffine.addX x x ℓ * (2 * y + W.a₁ * x + W.a₃) ^ 2
      = x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈

end Formalism.L2.Th1.A
