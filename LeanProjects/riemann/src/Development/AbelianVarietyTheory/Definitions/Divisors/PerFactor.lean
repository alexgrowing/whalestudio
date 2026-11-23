import Mathlib
noncomputable section
namespace GlobalTheory.PolDeg.Taut
variable (W : Type) [CommRing W] [IsDomain W]

def coordT (m N : ℕ) (k : Fin N) : MvPowerSeries (Fin N) W :=
  if (k : ℕ) < m then MvPowerSeries.X k else 1 + MvPowerSeries.X k

def params {m N : ℕ} (h : m ≤ N) : Fin m → MvPowerSeries (Fin N) W := fun i => MvPowerSeries.X (Fin.castLE h i)

def perFactor (m N n r : ℕ) (ε : Fin N → LinearMap.BilinForm ℤ (Fin r → ℤ)) (a b : Fin r → ℤ) : FractionRing (MvPowerSeries (Fin N) W) :=
  ∏ k, (algebraMap (MvPowerSeries (Fin N) W) (FractionRing (MvPowerSeries (Fin N) W)) (coordT W m N k)) ^ ((n : ℤ) * ε k a b)
example : perFactor W 0 0 3 0 (fun k => k.elim0) 0 0 = 1 := by simp [perFactor]
end GlobalTheory.PolDeg.Taut
