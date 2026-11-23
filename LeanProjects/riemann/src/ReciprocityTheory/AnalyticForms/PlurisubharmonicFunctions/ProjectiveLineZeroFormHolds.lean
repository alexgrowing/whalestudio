import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.GreenOfPoincareLelongHyperplane
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.LogInt
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.GreenCoord
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.HasCompactSupportCompHypInclAt

namespace ReciprocityTheory.AnForm.A

open MeasureTheory Filter Topology

theorem log_norm_integral_formula : PoincareLelongHyperplane := by
  intro n U v φ hp
  have hf : (hypInclAt (n := n) 0) = hypIncl := funext hypInclAt_zero
  have h := log_norm_integral_at_coordinate n 0 U v φ hp
  unfold densHypAt at h
  rw [hf] at h
  exact h

theorem log_norm_integral_formula_unit : PoincareLelongUnitPower := by
  intro n m U v φ u hp hu hu0
  obtain ⟨-, -, -, hsub, -⟩ := id hp
  obtain ⟨hI1, -, hE1⟩ := log_norm_integral_formula n U v φ hp
  obtain ⟨hI2, hE2⟩ := unit_part hp hu hu0
  have hae : (fun z : Fin (n + 1) → ℂ => Real.log ‖z 0 ^ m * u z‖ * densV v φ z) =ᵐ[volume]
      fun z => (m : ℝ) * (Real.log ‖z 0‖ * densV v φ z) + Real.log ‖u z‖ * densV v φ z := by
    filter_upwards [ae_coord_ne_zero (0 : Fin (n + 1))] with z hz
    by_cases hzv : z ∈ tsupport v
    · have huz : u z ≠ 0 := hu0 z (hsub hzv)
      rw [norm_mul, norm_zpow, Real.log_mul (zpow_ne_zero _ (norm_ne_zero_iff.mpr hz))
        (norm_ne_zero_iff.mpr huz), Real.log_zpow]
      ring
    · have h0 : densV v φ z = 0 := maDens_cons_eq_zero φ hzv
      rw [h0]
      ring
  refine ⟨((hI1.const_mul (m : ℝ)).add hI2).congr hae.symm, ?_⟩
  rw [integral_congr_ae hae, integral_add (hI1.const_mul _) hI2]
  first
    | rw [integral_const_mul]
    | rw [integral_mul_left]
  rw [hE1, hE2, add_zero]

theorem log_norm_integral_formula_snc : PoincareLelongNormalCrossing := by
  intro n m U v φ u hp hu hu0
  obtain ⟨-, -, -, hsub, -⟩ := id hp
  have hI : ∀ i, Integrable (fun z : Fin (n + 1) → ℂ => Real.log ‖z i‖ * densV v φ z) volume :=
    fun i => (log_norm_integral_at_coordinate n i U v φ hp).1
  have hE : ∀ i, ∫ z, Real.log ‖z i‖ * densV v φ z = ∫ w, v (hypInclAt i w) * densHypAt i φ w :=
    fun i => (log_norm_integral_at_coordinate n i U v φ hp).2.2
  obtain ⟨hIu, hEu⟩ := unit_part hp hu hu0
  have hIs : Integrable (fun z : Fin (n + 1) → ℂ =>
      ∑ i ∈ Finset.univ, (m i : ℝ) * (Real.log ‖z i‖ * densV v φ z)) volume :=
    integrable_finset_sum Finset.univ (fun i _ => (hI i).const_mul (m i : ℝ))
  have hae : (fun z : Fin (n + 1) → ℂ => Real.log ‖u z * ∏ i, z i ^ m i‖ * densV v φ z) =ᵐ[volume]
      fun z => Real.log ‖u z‖ * densV v φ z +
        ∑ i ∈ Finset.univ, (m i : ℝ) * (Real.log ‖z i‖ * densV v φ z) := by
    filter_upwards [ae_all_iff.mpr (fun i => ae_coord_ne_zero (n := n) i)] with z hz
    by_cases hzv : z ∈ tsupport v
    · have huz : u z ≠ 0 := hu0 z (hsub hzv)
      have hp0 : ‖∏ i, z i ^ m i‖ ≠ 0 := by
        rw [norm_ne_zero_iff]
        exact Finset.prod_ne_zero_iff.mpr (fun i _ => zpow_ne_zero _ (hz i))
      rw [norm_mul, Real.log_mul (norm_ne_zero_iff.mpr huz) hp0,
        log_norm_prod_zpow_eq_logMono m z hz, logMono, add_mul, Finset.sum_mul]
      congr 1
      refine Finset.sum_congr rfl (fun i _ => ?_)
      ring
    · have h0 : densV v φ z = 0 := maDens_cons_eq_zero φ hzv
      simp [h0]
  refine ⟨(hIu.add hIs).congr hae.symm, ?_⟩
  rw [integral_congr_ae hae, integral_add hIu hIs, hEu, zero_add,
    integral_finset_sum Finset.univ (fun i _ => (hI i).const_mul (m i : ℝ))]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  first
    | rw [integral_const_mul]
    | rw [integral_mul_left]
  rw [hE i]

end ReciprocityTheory.AnForm.A
