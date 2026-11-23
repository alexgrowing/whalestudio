import Mathlib

open PowerSeries

universe u

noncomputable section

namespace Formalism.ELL

def WFixed {R : Type u} [CommRing R] (W : WeierstrassCurve R) (w : PowerSeries R) : Prop :=
  constantCoeff w = 0 ∧
  w = X ^ 3 + C W.a₁ * X * w + C W.a₂ * X ^ 2 * w + C W.a₃ * w ^ 2 + C W.a₄ * X * w ^ 2
      + C W.a₆ * w ^ 3

def WSeriesUnique : Prop :=
  ∀ (R : Type u) [CommRing R] (W : WeierstrassCurve R), ∃! w : PowerSeries R, WFixed W w

def WSeriesLead : Prop :=
  ∀ (R : Type u) [CommRing R] (W : WeierstrassCurve R) (w : PowerSeries R), WFixed W w →
    coeff 0 w = 0 ∧ coeff 1 w = 0 ∧ coeff 2 w = 0 ∧ coeff 3 w = 1

section Points

variable {K : Type u} [Field K] {σ : Type}

def xOf (w : PowerSeries K) (s : MvPowerSeries σ K) : FractionRing (MvPowerSeries σ K) :=
  algebraMap (MvPowerSeries σ K) (FractionRing (MvPowerSeries σ K)) s /
    algebraMap (MvPowerSeries σ K) (FractionRing (MvPowerSeries σ K)) (w.subst s)

def yOf (w : PowerSeries K) (s : MvPowerSeries σ K) : FractionRing (MvPowerSeries σ K) :=
  -1 / algebraMap (MvPowerSeries σ K) (FractionRing (MvPowerSeries σ K)) (w.subst s)

end Points

def WPoint : Prop :=
  ∀ (K : Type u) [Field K] (W : WeierstrassCurve K) (w : PowerSeries K), WFixed W w →
    ∀ (σ : Type) [Finite σ] (s : MvPowerSeries σ K), MvPowerSeries.constantCoeff s = 0 → s ≠ 0 →
      (W.map (algebraMap K (FractionRing (MvPowerSeries σ K)))).toAffine.Nonsingular
        (xOf w s) (yOf w s)

def WFormalGroup : Prop :=
  ∀ (K : Type u) [Field K] (W : WeierstrassCurve K) (w : PowerSeries K), WFixed W w →
    ∃ F : FormalGroup K,
      (∀ d : Fin 2 →₀ ℕ, MvPowerSeries.coeff d F.toPowerSeries ∈
        Algebra.adjoin ℤ ({W.a₁, W.a₂, W.a₃, W.a₄, W.a₆} : Set K)) ∧
      let z₁ : MvPowerSeries (Fin 2) K := MvPowerSeries.X 0
      let z₂ : MvPowerSeries (Fin 2) K := MvPowerSeries.X 1
      let W' := (W.map (algebraMap K (FractionRing (MvPowerSeries (Fin 2) K)))).toAffine
      let ℓ := (yOf w z₁ - yOf w z₂) / (xOf w z₁ - xOf w z₂)
      xOf w F.toPowerSeries = W'.addX (xOf w z₁) (xOf w z₂) ℓ ∧
      yOf w F.toPowerSeries = W'.addY (xOf w z₁) (xOf w z₂) (yOf w z₁) ℓ

end Formalism.ELL
