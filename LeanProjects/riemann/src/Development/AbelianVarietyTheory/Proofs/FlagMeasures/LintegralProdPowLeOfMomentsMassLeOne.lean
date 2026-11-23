import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.OnePlaceKF
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DegVand
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsNormalFormStabilizerMeasure
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MomAllP
import Formalism.LocalRingCardinality.DataTies
open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp GlobalTheory.TypeAsm Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem lintegral_prod_pow_le_of_moments : ∀ (Ω : Type) [MeasurableSpace Ω] (ν : Measure Ω) (r q : ℕ) (ρ : Fin r → Ω → ℝ) (Ph : Ω → ℝ) (Rr : ℝ) (s : Finset (Fin r)), (∀ a, AEMeasurable (ρ a) ν) → (∀ a, ∀ᵐ x ∂ν, 0 ≤ ρ a x) → AEMeasurable Ph ν → (∀ x, 0 ≤ Ph x) → ∫⁻ x, ENNReal.ofReal (Ph x) ∂ν ≤ 1 → 1 ≤ Rr → (∀ a, ∫⁻ x, ENNReal.ofReal (ρ a x ^ (2 * (r * q)) * Ph x) ∂ν ≤ ENNReal.ofReal (Rr ^ (2 * (r * q)))) → ∫⁻ x, ENNReal.ofReal ((∏ a ∈ s, ρ a x) ^ (2 * q) * Ph x) ∂ν ≤ ENNReal.ofReal (Rr ^ (2 * (r * q))) := by
  classical
  intro Ω _ ν r q ρ Ph Rr s hρm hρ0 hPm hP0 hP1 hR hbd
  have hR0 : (0:ℝ) ≤ Rr := le_trans zero_le_one hR
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr
    have hs : s = ∅ := Finset.eq_empty_of_isEmpty s
    subst hs
    simpa using hP1
  · set N : ℕ := 2 * (r * q) with hN
    let u : Fin r → Ω → ℝ := fun a x => if a ∈ s then ρ a x else Rr
    have hrR : (0:ℝ) < r := by exact_mod_cast hr
    have hr0 : r ≠ 0 := Nat.pos_iff_ne_zero.mp hr
    have hpt : ∀ᵐ x ∂ν, ENNReal.ofReal ((∏ a ∈ s, ρ a x) ^ (2 * q) * Ph x)
        ≤ ∑ a : Fin r, ENNReal.ofReal ((r:ℝ)⁻¹) * ENNReal.ofReal (u a x ^ N * Ph x) := by
      have hall : ∀ᵐ x ∂ν, ∀ a, 0 ≤ ρ a x := ae_all_iff.mpr hρ0
      filter_upwards [hall] with x hx
      have hu0 : ∀ a, 0 ≤ u a x := fun a => by
        by_cases ha : a ∈ s <;> simp [u, ha, hx a, hR0]
      have h1 : (∏ a ∈ s, ρ a x) ^ (2 * q) ≤ ∏ a : Fin r, u a x ^ (2 * q) := by
        have : (∏ a ∈ s, ρ a x) ^ (2 * q)
            = ∏ a : Fin r, (if a ∈ s then ρ a x ^ (2 * q) else 1) := by
          rw [Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_pow]
        rw [this]
        apply Finset.prod_le_prod
        · intro a _
          by_cases ha : a ∈ s
          · simp [ha, pow_nonneg (hx a)]
          · simp [ha]
        · intro a _
          by_cases ha : a ∈ s
          · simp [u, ha]
          · simp [u, ha, one_le_pow₀ hR]
      have h2 : ∏ a : Fin r, u a x ^ (2 * q) ≤ ∑ a : Fin r, (r:ℝ)⁻¹ * u a x ^ N := by
        have hw : ∑ _a : Fin r, (r:ℝ)⁻¹ = 1 := by
          simp [Finset.card_univ, Fintype.card_fin, hrR.ne']
        have key := Real.geom_mean_le_arith_mean_weighted (Finset.univ : Finset (Fin r))
          (fun _ => (r:ℝ)⁻¹) (fun a => (u a x ^ (2 * q)) ^ r)
          (fun _ _ => inv_nonneg.mpr hrR.le) hw (fun a _ => pow_nonneg (pow_nonneg (hu0 a) _) _)
        have e1 : ∀ a, ((u a x ^ (2 * q)) ^ r) ^ ((r:ℝ)⁻¹) = u a x ^ (2 * q) := fun a =>
          Real.pow_rpow_inv_natCast (pow_nonneg (hu0 a) _) hr0
        have e2 : ∀ a, (u a x ^ (2 * q)) ^ r = u a x ^ N := fun a => by
          rw [← pow_mul, hN]; congr 1; ring
        simp only [e1] at key
        simp only [e2] at key
        exact key
      have hP : 0 ≤ Ph x := hP0 x
      have h3 : (∏ a ∈ s, ρ a x) ^ (2 * q) * Ph x
          ≤ ∑ a : Fin r, (r:ℝ)⁻¹ * (u a x ^ N * Ph x) := by
        calc (∏ a ∈ s, ρ a x) ^ (2 * q) * Ph x
            ≤ (∑ a : Fin r, (r:ℝ)⁻¹ * u a x ^ N) * Ph x :=
              mul_le_mul_of_nonneg_right (h1.trans h2) hP
          _ = ∑ a : Fin r, (r:ℝ)⁻¹ * (u a x ^ N * Ph x) := by
              rw [Finset.sum_mul]; congr 1; ext a; ring
      calc ENNReal.ofReal ((∏ a ∈ s, ρ a x) ^ (2 * q) * Ph x)
          ≤ ENNReal.ofReal (∑ a : Fin r, (r:ℝ)⁻¹ * (u a x ^ N * Ph x)) :=
            ENNReal.ofReal_le_ofReal h3
        _ = ∑ a : Fin r, ENNReal.ofReal ((r:ℝ)⁻¹) * ENNReal.ofReal (u a x ^ N * Ph x) := by
            rw [ENNReal.ofReal_sum_of_nonneg]
            · congr 1; ext a
              rw [ENNReal.ofReal_mul (inv_nonneg.mpr hrR.le)]
            · intro a _
              exact mul_nonneg (inv_nonneg.mpr hrR.le) (mul_nonneg (pow_nonneg (hu0 a) _) hP)
    have hum : ∀ a, AEMeasurable (u a) ν := fun a => by
      by_cases ha : a ∈ s
      · simpa [u, ha] using hρm a
      · simp only [u, ha, if_false]; exact aemeasurable_const
    have hint : ∀ a, ∫⁻ x, ENNReal.ofReal (u a x ^ N * Ph x) ∂ν ≤ ENNReal.ofReal (Rr ^ N) := by
      intro a
      by_cases ha : a ∈ s
      · simpa [u, ha] using hbd a
      · simp only [u, ha, if_false]
        have hRN : (0:ℝ) ≤ Rr ^ N := pow_nonneg hR0 _
        simp_rw [ENNReal.ofReal_mul hRN]
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        calc ENNReal.ofReal (Rr ^ N) * ∫⁻ x, ENNReal.ofReal (Ph x) ∂ν
            ≤ ENNReal.ofReal (Rr ^ N) * 1 := by gcongr
          _ = ENNReal.ofReal (Rr ^ N) := mul_one _
    calc ∫⁻ x, ENNReal.ofReal ((∏ a ∈ s, ρ a x) ^ (2 * q) * Ph x) ∂ν
        ≤ ∫⁻ x, ∑ a : Fin r, ENNReal.ofReal ((r:ℝ)⁻¹) * ENNReal.ofReal (u a x ^ N * Ph x) ∂ν :=
          lintegral_mono_ae hpt
      _ = ∑ a : Fin r, ENNReal.ofReal ((r:ℝ)⁻¹) * ∫⁻ x, ENNReal.ofReal (u a x ^ N * Ph x) ∂ν := by
          rw [lintegral_finset_sum']
          · congr 1; ext a
            rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          · intro a _
            exact (((hum a).pow_const N).mul hPm).ennreal_ofReal.const_mul _
      _ ≤ ∑ _a : Fin r, ENNReal.ofReal ((r:ℝ)⁻¹) * ENNReal.ofReal (Rr ^ N) := by
          gcongr with a
          exact hint a
      _ = ENNReal.ofReal (Rr ^ N) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_assoc]
          have : (r : ℝ≥0∞) * ENNReal.ofReal ((r:ℝ)⁻¹) = 1 := by
            rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg r),
              mul_inv_cancel₀ hrR.ne', ENNReal.ofReal_one]
          rw [this, one_mul]

end GlobalTheory
