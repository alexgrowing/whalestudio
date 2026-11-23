import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMemberP
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Poinc.LeastVec

def cross {s : ℕ} (W : Matrix (Fin s) (Fin s) ℤ) {X : Type} [AddCommGroup X] (β : LinearMap.BilinForm ℤ X)
    (x y : Fin s → X) : ℤ :=
  ∑ u, ∑ v, W u v * (β (x u) (y v) + β (y u) (x v))

theorem qW_add_zsmul {s : ℕ} (W : Matrix (Fin s) (Fin s) ℤ) {X : Type} [AddCommGroup X] (β : LinearMap.BilinForm ℤ X)
    (x y : Fin s → X) (n : ℤ) :
    qW W β (x + n • y) = qW W β x + n * cross W β x y + n ^ 2 * qW W β y := by
  unfold qW cross
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp only [Pi.add_apply, Pi.smul_apply, map_add, LinearMap.add_apply, map_zsmul, LinearMap.smul_apply, smul_eq_mul]
  ring

theorem least_lt_add_smul : ∀ (s : ℕ) (W : Matrix (Fin s) (Fin s) ℤ), PosW W → ∀ (X : Type) [AddCommGroup X] (β : LinearMap.BilinForm ℤ X), (∀ a b, β a b = β b a) → (∀ a, 0 ≤ β a a) → ∀ (H : AddSubgroup (Fin s → X)), (∀ mu ∈ H, mu ≠ 0 → 0 < qW W β mu) → ∀ mu₀ ∈ H, mu₀ ≠ 0 → (∀ mu ∈ H, mu ≠ 0 → qW W β mu₀ ≤ qW W β mu) → ∀ N₁ : ℕ, 3 ≤ N₁ → ∀ nu ∈ H, nu ≠ 0 → qW W β mu₀ < qW W β (mu₀ + N₁ • nu) := by
  intro s W hW X _ β hs hβ H hpos mu₀ hmu₀ _ hmin N₁ hN nu hnu hnu0
  have hq := qW_add_zsmul W β mu₀ nu
  have h1 : 0 ≤ qW W β (mu₀ + nu) := qW_nonneg hW hs hβ _
  rw [← one_zsmul nu, hq 1] at h1
  simp only [one_mul, one_pow] at h1
  have hN' : qW W β (mu₀ + N₁ • nu) = qW W β mu₀ + (N₁ : ℤ) * cross W β mu₀ nu + (N₁ : ℤ) ^ 2 * qW W β nu := by
    rw [← hq, natCast_zsmul]
  rw [hN']
  have hle := hmin nu hnu hnu0
  have hp := hpos nu hnu hnu0
  have hN3 : (3 : ℤ) ≤ N₁ := by exact_mod_cast hN
  set B := cross W β mu₀ nu
  set q0 := qW W β mu₀
  set qn := qW W β nu
  have hNn : (0 : ℤ) ≤ N₁ := by omega
  have e1 : (N₁ : ℤ) * (-q0 - qn) ≤ (N₁ : ℤ) * B := mul_le_mul_of_nonneg_left (by linarith) hNn
  have e2 : (N₁ : ℤ) * q0 ≤ (N₁ : ℤ) * qn := mul_le_mul_of_nonneg_left hle hNn
  have e3 : 0 < (N₁ : ℤ) * ((N₁ : ℤ) - 2) * qn := by
    apply mul_pos (mul_pos (by omega) (by omega)) hp
  nlinarith

end GlobalTheory.Poinc.LeastVec
