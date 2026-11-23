import Formalism.FormalGroupLog.Statement

noncomputable section

open PowerSeries

universe u v

namespace Formalism.LT

open Formalism.G

def DivByMv {K : Type u} [NormedField K] {ι : Type v} (x : K) (F : MvPowerSeries ι K) : Prop :=
  ∀ d : ι →₀ ℕ, ‖MvPowerSeries.coeff d F‖ ≤ ‖x‖

def SolveExists : Prop :=
  ∀ (R : Type u) [CommRing R] (ι : Type v) [Finite ι] (f : PowerSeries R)
    (G : MvPowerSeries ι R),
    constantCoeff f = 0 → coeff 1 f = 1 → MvPowerSeries.constantCoeff G = 0 →
      ∃ h : MvPowerSeries ι R, MvPowerSeries.constantCoeff h = 0 ∧ f.subst h = G

def InvIntegralOfClass : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] (ι : Type v) [Finite ι]
    (C : MvPowerSeries ι K → Prop) (f : PowerSeries K),
    constantCoeff f = 0 → coeff 1 f = 1 →
    (∀ a b, C a → C b → C (a - b)) →
    (∀ P : MvPowerSeries ι K, MvPowerSeries.constantCoeff P = 0 → IntegralMv P →
      C (f.subst P)) →
    (∀ D, C D → ∀ N : ℕ, 1 ≤ N →
      (∀ d : ι →₀ ℕ, d.degree < N → MvPowerSeries.coeff d D = 0) →
      ∀ d : ι →₀ ℕ, d.degree = N → ‖MvPowerSeries.coeff d D‖ ≤ 1) →
    ∀ h : MvPowerSeries ι K, MvPowerSeries.constantCoeff h = 0 → C (f.subst h) → IntegralMv h

def FunEqLowCoeff : Prop :=
  ∀ (K : Type u) [NormedField K] (ι : Type v) (p q : ℕ) (hq : q ≠ 0) (σ : K →+* K), 2 ≤ q →
    ∀ D : MvPowerSeries ι K, IsFunEqTypeMv p q hq σ D → ∀ N : ℕ, 1 ≤ N →
      (∀ d : ι →₀ ℕ, d.degree < N → MvPowerSeries.coeff d D = 0) →
      ∀ d : ι →₀ ℕ, d.degree = N → ‖MvPowerSeries.coeff d D‖ ≤ 1

def IntegralSubst : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] (ι : Type v) (f : PowerSeries K)
    (P : MvPowerSeries ι K),
    IntegralPS f → MvPowerSeries.constantCoeff P = 0 → IntegralMv P → IntegralMv (f.subst P)

def CoeffBound : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CharZero K] (p q : ℕ) (σ : K →+* K),
    FunctionalEquationSetting K p q σ →
    ∀ f : PowerSeries K, constantCoeff f = 0 → IsFunEqType p q σ f →
      ∀ n : ℕ, ∃ k : ℕ, q ^ k ∣ n ∧ ‖coeff n f‖ * ‖(p : K)‖ ^ k ≤ 1

def PowCongr : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] (ι : Type v) (p : ℕ), p.Prime →
    ∀ A B : MvPowerSeries ι K, IntegralMv A → IntegralMv B → ∀ r : ℕ, 1 ≤ r →
      DivByMv ((p : K) ^ r) (A - B) →
      ∀ j m : ℕ, DivByMv ((p : K) ^ (r + j)) (A ^ (p ^ j * m) - B ^ (p ^ j * m))

def FrobCongr : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CharZero K] (p q : ℕ) (hq : q ≠ 0)
    (σ : K →+* K), FunctionalEquationSetting K p q σ →
    ∀ (ι : Type v) (A : MvPowerSeries ι K), IntegralMv A →
      DivByMv (p : K) (A ^ q - MvPowerSeries.expand q hq (MvPowerSeries.map σ A))

end Formalism.LT
