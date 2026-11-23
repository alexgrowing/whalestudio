import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.PowerSeriesHasSumAt
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.PowerSeriesEvalTsumUnitDiscPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NormCoeffIntegralPowerSeriesLeProdZerosStatement

open GlobalTheory.ConvSer

namespace GlobalTheory.ConvSer

private theorem intg_of_norm_coeff_le_one {K : Type} [NormedField K] (f : PowerSeries K)
    (h : ∀ n, ‖PowerSeries.coeff n f‖ ≤ 1) : Intg f := by
  intro ν
  have h1 := h (ν ())
  have h2 : ν = Finsupp.single () (ν ()) := Finsupp.unique_single ν
  rw [h2]
  exact h1

theorem integralPowerSeries_eq_zero_of_vanish_on_points (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (G : ℕ → Finset K) (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1)
    (hG : ∀ n, ∀ x ∈ G n, r ≤ ‖x‖ ∧ ‖x‖ < 1)
    (hT : Filter.Tendsto (fun n => ∏ x ∈ G n, ‖x‖) Filter.atTop (nhds 0))
    (h : PowerSeries K) (hh : Intg h) (m : ℕ)
    (hz : ∀ n, m ≤ n → ∀ x ∈ G n, ev1 h x = 0) : h = 0 := by
  ext k
  have key : ‖PowerSeries.coeff k h‖ * r ^ k ≤ 0 := by
    refine ge_of_tendsto hT ?_
    filter_upwards [Filter.eventually_ge_atTop m] with n hn
    exact (GlobalTheory.T.norm_coeff_integral_powerSeries_le_prod_zeros K h (G n) hh (fun x hx => ⟨(hG n x hx).2, hz n hn x hx⟩)).1 r hr hr1
      (fun x hx => (hG n x hx).1) k
  have hp : 0 < r ^ k := pow_pos hr k
  have h0 : ‖PowerSeries.coeff k h‖ ≤ 0 := by
    by_contra hc
    push Not at hc
    have := mul_pos hc hp
    linarith
  simpa using norm_le_zero_iff.mp h0

theorem eq_zero_of_ev_vanish : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] (G : ℕ → Finset K) (r : ℝ), 0 < r → r ≤ 1 → Monotone G → (∀ n, ∀ x ∈ G n, r ≤ ‖x‖ ∧ ‖x‖ < 1) → Filter.Tendsto (fun n => ∏ x ∈ G n, ‖x‖) Filter.atTop (nhds 0) → ∀ H : MvPowerSeries (Fin 2) K, Intg H → (∀ n, ∀ x ∈ G n, ∀ y ∈ G n, ev H ![x, y] = 0) → H = 0 := by
  intro K _ _ _ G r hr hr1 hmono hG hT H hH hz
  have hS : ∀ (x y : K), ‖x‖ < 1 → ‖y‖ < 1 →
      Intg (shift1 H y) ∧ ev1 (shift1 H y) x = ev H ![x, y] := fun x y hx hy =>
    (GlobalTheory.T.powerSeriesEvalTsum_unitDisc_properties_alt K x hx).2.2.2.2.2.2.2.2.2.1 H y hy hH
  have h1 : ∀ m, ∀ y ∈ G m, shift1 H y = 0 := by
    intro m y hy
    have hy1 := (hG m y hy).2
    refine integralPowerSeries_eq_zero_of_vanish_on_points K G r hr hr1 hG hT _ (hS 0 y (by simp) hy1).1 m ?_
    intro n hn x hx
    rw [(hS x y (hG n x hx).2 hy1).2]
    exact hz n x hx y (hmono hn hy)
  have h2 : ∀ a b : ℕ,
      MvPowerSeries.coeff (Finsupp.single 0 a + Finsupp.single 1 b) H = 0 := by
    intro a b
    have h3 : (PowerSeries.mk fun b : ℕ =>
        MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) a + Finsupp.single 1 b) H) = 0 := by
      refine integralPowerSeries_eq_zero_of_vanish_on_points K G r hr hr1 hG hT _ (intg_of_norm_coeff_le_one _ ?_) 0 ?_
      · intro n
        rw [PowerSeries.coeff_mk]
        exact hH _
      · intro n _ y hy
        have h4 := congrArg (PowerSeries.coeff a) (h1 n y hy)
        rw [shift1, PowerSeries.coeff_mk, map_zero] at h4
        simpa [ev1, PowerSeries.coeff_mk] using h4
    have h5 := congrArg (PowerSeries.coeff b) h3
    rwa [PowerSeries.coeff_mk, map_zero] at h5
  ext ν
  have hν : ν = Finsupp.single 0 (ν 0) + Finsupp.single 1 (ν 1) := by
    ext i
    fin_cases i <;> simp
  rw [hν, h2]
  simp

end GlobalTheory.ConvSer
