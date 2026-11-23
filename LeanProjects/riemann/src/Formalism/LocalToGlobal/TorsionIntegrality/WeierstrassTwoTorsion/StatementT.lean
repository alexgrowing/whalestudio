import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.CompInv

open PowerSeries

universe u v

noncomputable section

namespace Formalism.L2.Th1.A

def DLCoeff : Prop :=
  ∀ (R : Type u) [CommRing R] (f : LaurentSeries R) (n : ℤ),
    (dL f).coeff n = ((n + 1 : ℤ) : R) * f.coeff (n + 1)

def DLLeibniz : Prop :=
  ∀ (R : Type u) [CommRing R] (f g : LaurentSeries R), dL (f * g) = f * dL g + g * dL f

def DLCoe : Prop :=
  ∀ (R : Type u) [CommRing R] (f : R⟦X⟧), dL (toL f) = toL (derivative R f)

def UPowRules : Prop :=
  ∀ (R : Type u) [CommRing R],
    (uPow 0 : LaurentSeries R) = 1 ∧ (uPow 1 : LaurentSeries R) = toL X ∧
    (∀ m n : ℤ, (uPow (m + n) : LaurentSeries R) = uPow m * uPow n) ∧
    (∀ n : ℤ, dL (uPow n : LaurentSeries R) = HahnSeries.C ((n : ℤ) : R) * uPow (n - 1)) ∧
    (∀ r : R, dL (HahnSeries.C r : LaurentSeries R) = 0) ∧
    (∀ r : R, toL (C r) = (HahnSeries.C r : LaurentSeries R))

def ToLInjective : Prop :=
  ∀ (R : Type u) [CommRing R],
    Function.Injective (toL : R⟦X⟧ → LaurentSeries R) ∧
    ∀ (n : ℤ) (f g : LaurentSeries R), uPow n * f = uPow n * g → f = g

def CompInvSpec : Prop :=
  ∀ (R : Type u) [CommRing R] (s : R⟦X⟧), constantCoeff s = 0 → IsUnit (coeff 1 s) →
    constantCoeff (compInv s) = 0 ∧ s.subst (compInv s) = X ∧ (compInv s).subst s = X ∧
    coeff 1 (compInv s) * coeff 1 s = 1 ∧
    (∀ t : R⟦X⟧, constantCoeff t = 0 → s.subst t = X → t = compInv s) ∧
    (∀ t : R⟦X⟧, constantCoeff t = 0 → t.subst s = X → t = compInv s)

def CompInvMap : Prop :=
  ∀ (R : Type u) (S : Type v) [CommRing R] [CommRing S] (φ : R →+* S) (s : R⟦X⟧),
    constantCoeff s = 0 → IsUnit (coeff 1 s) →
    PowerSeries.map φ (compInv s) = compInv (PowerSeries.map φ s)

def IntegSpec : Prop :=
  ∀ (K : Type u) [Field K] [CharZero K] (f : K⟦X⟧),
    constantCoeff (integ f) = 0 ∧ derivative K (integ f) = f ∧
    ∀ g : K⟦X⟧, constantCoeff g = 0 → derivative K g = f → g = integ f

end Formalism.L2.Th1.A
