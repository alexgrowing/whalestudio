import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CentreAtOfIsAt
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep GlobalTheory.FieldPair

namespace GlobalTheory

theorem elementary_binom_bound : ∀ (c k : ℕ) (h d : ℚ), 1 ≤ k → 0 < h → (c : ℚ) * (k : ℚ) ^ k < h ^ k * d →
  ∃ q : ℚ, q < d ∧ ∀ l₀ : ℕ, ∃ l M : ℕ, l₀ ≤ l ∧ 1 ≤ M ∧ (k : ℚ) * l < h * M ∧ h < l ∧
    ((c * (M + k - 1).choose k : ℕ) : ℚ) < q * (l : ℚ) ^ k / k.factorial := by
  intro c k h d hk hh hcd
  have hhk : 0 < h ^ k := pow_pos hh k
  set a : ℚ := (c : ℚ) * ((k : ℚ) / h) ^ k with ha
  have had : a < d := by
    rw [ha, div_pow, ← mul_div_assoc, div_lt_iff₀ hhk]; linarith
  refine ⟨(a + d) / 2, by linarith, ?_⟩
  intro l₀
  have hlim : Tendsto (fun l : ℕ => (c : ℚ) * ((k : ℚ) / h + (k : ℚ) / (l : ℚ)) ^ k) atTop
      (nhds ((c : ℚ) * ((k : ℚ) / h + 0) ^ k)) :=
    ((tendsto_const_nhds.add (tendsto_const_div_atTop_nhds_zero_nat (k : ℚ))).pow k).const_mul _
  rw [add_zero] at hlim
  have hev1 : ∀ᶠ l : ℕ in atTop, (c : ℚ) * ((k : ℚ) / h + (k : ℚ) / (l : ℚ)) ^ k < (a + d) / 2 :=
    hlim.eventually (gt_mem_nhds (by rw [← ha]; linarith))
  have hev2 : ∀ᶠ l : ℕ in atTop, h < (l : ℚ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop h)
  obtain ⟨l, hl1, hl2, hl0⟩ := (hev1.and (hev2.and (eventually_ge_atTop l₀))).exists
  have hlpos : (0 : ℚ) < l := lt_trans hh hl2
  set x : ℚ := (k : ℚ) * l / h with hx
  have hx0 : 0 ≤ x := by positivity
  refine ⟨l, ⌊x⌋₊ + 1, hl0, by omega, ?_, hl2, ?_⟩
  · have := Nat.lt_floor_add_one x
    push_cast
    rw [hx, div_lt_iff₀ hh] at this
    linarith
  · have hfl : ((⌊x⌋₊ : ℕ) : ℚ) ≤ x := Nat.floor_le hx0
    have hcast : (((⌊x⌋₊ + 1 + k - 1 : ℕ)) : ℚ) = (⌊x⌋₊ : ℚ) + k := by
      have : ⌊x⌋₊ + 1 + k - 1 = ⌊x⌋₊ + k := by omega
      rw [this]; push_cast; ring
    have hch : (((⌊x⌋₊ + 1 + k - 1).choose k : ℕ) : ℚ) ≤ (((⌊x⌋₊ + 1 + k - 1 : ℕ)) : ℚ) ^ k / k.factorial :=
      Nat.choose_le_pow_div k _
    have hfact : (0 : ℚ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
    have hbase : (((⌊x⌋₊ + 1 + k - 1 : ℕ)) : ℚ) ≤ (l : ℚ) * ((k : ℚ) / h + (k : ℚ) / (l : ℚ)) := by
      rw [hcast, mul_add, hx]
      have e1 : (l : ℚ) * ((k : ℚ) / h) = (k : ℚ) * l / h := by ring
      have e2 : (l : ℚ) * ((k : ℚ) / l) = k := by field_simp
      rw [e1, e2]; linarith [hfl]
    have hpow : (((⌊x⌋₊ + 1 + k - 1 : ℕ)) : ℚ) ^ k ≤ ((l : ℚ) * ((k : ℚ) / h + (k : ℚ) / (l : ℚ))) ^ k :=
      pow_le_pow_left₀ (by positivity) hbase k
    have hlk : (0 : ℚ) < (l : ℚ) ^ k := pow_pos hlpos k
    push_cast
    calc (c : ℚ) * (((⌊x⌋₊ + 1 + k - 1).choose k : ℕ) : ℚ)
        ≤ (c : ℚ) * ((((⌊x⌋₊ + 1 + k - 1 : ℕ)) : ℚ) ^ k / k.factorial) :=
          mul_le_mul_of_nonneg_left hch (by positivity)
      _ ≤ (c : ℚ) * (((l : ℚ) * ((k : ℚ) / h + (k : ℚ) / (l : ℚ))) ^ k / k.factorial) := by
          gcongr
      _ = ((c : ℚ) * ((k : ℚ) / h + (k : ℚ) / (l : ℚ)) ^ k) * (l : ℚ) ^ k / k.factorial := by
          rw [mul_pow]; ring
      _ < (a + d) / 2 * (l : ℚ) ^ k / k.factorial := by
          apply div_lt_div_of_pos_right _ hfact
          exact mul_lt_mul_of_pos_right hl1 hlk

end GlobalTheory
