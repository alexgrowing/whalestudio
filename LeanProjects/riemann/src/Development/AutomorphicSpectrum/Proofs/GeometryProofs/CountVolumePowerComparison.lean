import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ModelSmall
import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.VolumeInputs
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.OverLaUnique
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi

open scoped ENNReal

namespace GlobalTheory.CompanionTheory.Ar.Plug

theorem logCard_pow_le (x : ℕ∞) {d : ℕ} (hd : 0 < d) :
    GlobalTheory.CompHt.logCard (x ^ d) ≤ (d : ℝ≥0∞) * GlobalTheory.CompHt.logCard x := by
  induction x using ENat.recTopCoe with
  | top =>
    rw [GlobalTheory.CompHt.logCard_top, ENNReal.mul_top (Nat.cast_ne_zero.2 hd.ne')]
    exact le_top
  | coe a =>
    have h : ((a : ℕ∞) ^ d) = ((a ^ d : ℕ) : ℕ∞) := by push_cast; rfl
    rw [h, GlobalTheory.CompHt.logCard_coe, GlobalTheory.CompHt.logCard_coe, Nat.cast_pow, Real.log_pow,
      ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]

theorem logCard_mono {x y : ℕ∞} (h : x ≤ y) : GlobalTheory.CompHt.logCard x ≤ GlobalTheory.CompHt.logCard y :=
  EReal.toENNReal_le_toENNReal (ENNReal.log_monotone (ENat.toENNReal_le.2 h))

theorem natCast_shift_pow (D j k : ℕ) (hk : 0 < k) :
    ((8 * (k + j) : ℕ) : ℝ≥0∞) ^ (D + 1) =
      ENNReal.ofReal ((1 + (j : ℝ) / k) ^ (D + 1)) * ((8 * k : ℕ) : ℝ≥0∞) ^ (D + 1) := by
  have hk' : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
  have hj : (0 : ℝ) ≤ 1 + (j : ℝ) / k := by positivity
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_pow (Nat.cast_nonneg _),
    ← ENNReal.ofReal_pow (Nat.cast_nonneg _), ← ENNReal.ofReal_mul (by positivity), ← mul_pow]
  congr 2
  push_cast
  field_simp

theorem tendsto_shift_ratio (D j : ℕ) :
    Tendsto (fun k : ℕ => ENNReal.ofReal ((1 + (j : ℝ) / k) ^ (D + 1))) atTop (𝓝 1) := by
  have h : Tendsto (fun k : ℕ => (j : ℝ) / k) atTop (𝓝 0) := tendsto_const_div_atTop_nhds_zero_nat _
  have h2 : Tendsto (fun k : ℕ => (1 + (j : ℝ) / k) ^ (D + 1)) atTop (𝓝 ((1 + 0) ^ (D + 1))) :=
    (tendsto_const_nhds.add h).pow _
  have h3 := ENNReal.tendsto_ofReal h2
  simpa using h3

theorem term_le_shift (D n d j k : ℕ) (hn : 0 < n) (hd : 0 < d) (hk : 0 < k) {x y : ℕ∞} (h : x ≤ y ^ d) :
    (D.factorial : ℝ≥0∞) * GlobalTheory.CompHt.logCard x / (((n * d : ℕ) : ℝ≥0∞) * ((8 * k : ℕ) : ℝ≥0∞) ^ (D + 1)) ≤
      (D.factorial : ℝ≥0∞) * GlobalTheory.CompHt.logCard y / ((n : ℝ≥0∞) * ((8 * (k + j) : ℕ) : ℝ≥0∞) ^ (D + 1)) *
        ENNReal.ofReal ((1 + (j : ℝ) / k) ^ (D + 1)) := by
  set A : ℝ≥0∞ := ((8 * k : ℕ) : ℝ≥0∞) ^ (D + 1) with hA
  set A' : ℝ≥0∞ := ((8 * (k + j) : ℕ) : ℝ≥0∞) ^ (D + 1) with hA'
  set c : ℝ≥0∞ := ENNReal.ofReal ((1 + (j : ℝ) / k) ^ (D + 1)) with hc
  have hcA : A' = c * A := natCast_shift_pow D j k hk
  have hA0 : A ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (by omega))
  have hAt : A ≠ ⊤ := ENNReal.pow_ne_top (ENNReal.natCast_ne_top _)
  have hA'0 : A' ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (by omega))
  have hA't : A' ≠ ⊤ := ENNReal.pow_ne_top (ENNReal.natCast_ne_top _)
  have hn0 : (n : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  have hnt : (n : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hd0 : (d : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.2 hd.ne'
  have hdt : (d : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hL : GlobalTheory.CompHt.logCard x ≤ (d : ℝ≥0∞) * GlobalTheory.CompHt.logCard y :=
    (logCard_mono h).trans (logCard_pow_le y hd)
  refine ENNReal.div_le_of_le_mul ?_
  have key : (D.factorial : ℝ≥0∞) * GlobalTheory.CompHt.logCard y / ((n : ℝ≥0∞) * A') * c * (((n * d : ℕ) : ℝ≥0∞) * A) =
      (D.factorial : ℝ≥0∞) * ((d : ℝ≥0∞) * GlobalTheory.CompHt.logCard y) := by
    rw [div_eq_mul_inv, ENNReal.mul_inv (Or.inl hn0) (Or.inl hnt), Nat.cast_mul]
    calc _ = (D.factorial : ℝ≥0∞) * ((d : ℝ≥0∞) * GlobalTheory.CompHt.logCard y) * ((n : ℝ≥0∞)⁻¹ * n) * ((A')⁻¹ * (c * A)) := by
          ring
      _ = _ := by
          rw [← hcA, ENNReal.inv_mul_cancel hn0 hnt, ENNReal.inv_mul_cancel hA'0 hA't, mul_one, mul_one]
  rw [key]
  gcongr

theorem countVol_le_of_le_shift_pow : ∀ (D n d k₀ : ℕ) (m m' : ℕ → ℕ∞), 0 < n → 0 < d → 8 ∣ k₀ →
    (∀ᶠ τ : ℕ in atTop, m τ ≤ m' (τ + k₀) ^ d) →
    GlobalTheory.CompHt.countVol D (n * d) 8 m ≤ GlobalTheory.CompHt.countVol D n 8 m' := by
  rintro D n d _ m m' hn hd ⟨j, rfl⟩ h
  obtain ⟨N, hN⟩ := eventually_atTop.1 h
  set b : ℕ → ℝ≥0∞ := fun k => (D.factorial : ℝ≥0∞) * GlobalTheory.CompHt.logCard (m' (8 * k)) /
    ((n : ℝ≥0∞) * ((8 * k : ℕ) : ℝ≥0∞) ^ (D + 1)) with hb
  set c : ℕ → ℝ≥0∞ := fun k => ENNReal.ofReal ((1 + (j : ℝ) / k) ^ (D + 1)) with hc
  have hlim : limsup c atTop = 1 := (tendsto_shift_ratio D j).limsup_eq
  have hle : GlobalTheory.CompHt.countVol D (n * d) 8 m ≤ limsup ((fun k => b (k + j)) * c) atTop := by
    refine limsup_le_limsup ?_
    filter_upwards [eventually_ge_atTop (N + 1)] with k hk
    have hx : m (8 * k) ≤ m' (8 * (k + j)) ^ d := by
      have := hN (8 * k) (by omega)
      rwa [show 8 * k + 8 * j = 8 * (k + j) by ring] at this
    exact term_le_shift D n d j k hn hd (by omega) hx
  refine hle.trans ((ENNReal.limsup_mul_le' (Or.inr (by simp [hlim])) (Or.inr (by simp [hlim]))).trans ?_)
  rw [hlim, mul_one, Filter.limsup_nat_add b j]
  rfl

end GlobalTheory.CompanionTheory.Ar.Plug
