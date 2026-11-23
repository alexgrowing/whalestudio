import Mathlib

noncomputable section

namespace GlobalTheory.ConvSer

def Intg {σ K : Type*} [NormedField K] (S : MvPowerSeries σ K) : Prop :=
  ∀ ν, ‖MvPowerSeries.coeff ν S‖ ≤ 1

def Bdd {σ K : Type*} [NormedField K] (S : MvPowerSeries σ K) : Prop :=
  ∃ C : ℝ, ∀ ν, ‖MvPowerSeries.coeff ν S‖ ≤ C

def Small {σ K : Type*} [NormedField K] (s : MvPowerSeries σ K) : Prop :=
  Intg s ∧ ‖MvPowerSeries.constantCoeff s‖ < 1

def HS {σ K : Type*} [Fintype σ] [NormedField K] (S : MvPowerSeries σ K) (x : σ → K) (a : K) : Prop :=
  HasSum (fun ν : σ →₀ ℕ => MvPowerSeries.coeff ν S * ∏ i, x i ^ ν i) a

def PowerSeriesHasSumAt {K : Type*} [NormedField K] (f : PowerSeries K) (t a : K) : Prop :=
  HasSum (fun n : ℕ => PowerSeries.coeff n f * t ^ n) a

def ev {σ K : Type*} [Fintype σ] [NormedField K] (S : MvPowerSeries σ K) (x : σ → K) : K :=
  ∑' ν : σ →₀ ℕ, MvPowerSeries.coeff ν S * ∏ i, x i ^ ν i

def ev1 {K : Type*} [NormedField K] (f : PowerSeries K) (t : K) : K :=
  ∑' n : ℕ, PowerSeries.coeff n f * t ^ n

def csub {σ τ K : Type*} [Fintype σ] [NormedField K] (s : σ → MvPowerSeries τ K)
    (S : MvPowerSeries σ K) : MvPowerSeries τ K :=
  fun μ => ∑' ν : σ →₀ ℕ, MvPowerSeries.coeff ν S * MvPowerSeries.coeff μ (∏ i, s i ^ ν i)

def csub1 {τ K : Type*} [NormedField K] (s : MvPowerSeries τ K) (f : PowerSeries K) :
    MvPowerSeries τ K :=
  fun μ => ∑' n : ℕ, PowerSeries.coeff n f * MvPowerSeries.coeff μ (s ^ n)

def shift1 {K : Type*} [NormedField K] (F : MvPowerSeries (Fin 2) K) (y : K) : PowerSeries K :=
  PowerSeries.mk fun a => ∑' b : ℕ,
    MvPowerSeries.coeff (Finsupp.single 0 a + Finsupp.single 1 b) F * y ^ b

def ChordRel {R : Type*} [CommRing R] (u₁ w₁ u₂ w₂ u₃ w₃ : R) : Prop :=
  u₃ * (u₁ * w₂ - u₂ * w₁) ^ 2 * w₁ * w₂ =
      w₃ * ((w₁ - w₂) ^ 2 * w₁ * w₂ - (u₁ * w₂ + u₂ * w₁) * (u₁ * w₂ - u₂ * w₁) ^ 2) ∧
    w₁ * (u₁ * w₂ - u₂ * w₁) = (w₁ - w₂) * (u₃ * w₁ - u₁ * w₃) - w₃ * (u₁ * w₂ - u₂ * w₁)

def IsW {R : Type*} [CommRing R] (a b : R) (w : PowerSeries R) : Prop :=
  PowerSeries.constantCoeff w = 0 ∧
    w = PowerSeries.X ^ 3 + PowerSeries.C a * PowerSeries.X * w ^ 2 + PowerSeries.C b * w ^ 3

def uP (L : PeriodPair) (z : ℂ) : ℂ := -(2 * L.weierstrassP z) / L.derivWeierstrassP z

def wP (L : PeriodPair) (z : ℂ) : ℂ := -2 / L.derivWeierstrassP z

def nMul {R : Type*} [CommRing R] (F : FormalGroup R) (n : ℕ) : PowerSeries R :=
  Nat.rec (motive := fun _ => PowerSeries R) 0
    (fun _ g => MvPowerSeries.subst (![g, PowerSeries.X] : Fin 2 → MvPowerSeries Unit R)
      F.toPowerSeries) n

theorem nMul_zero {R : Type*} [CommRing R] (F : FormalGroup R) : nMul F 0 = 0 := rfl

theorem nMul_succ {R : Type*} [CommRing R] (F : FormalGroup R) (n : ℕ) :
    nMul F (n + 1) = MvPowerSeries.subst
      (![nMul F n, PowerSeries.X] : Fin 2 → MvPowerSeries Unit R) F.toPowerSeries := rfl

end GlobalTheory.ConvSer
