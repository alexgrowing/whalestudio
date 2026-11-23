import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.ThStmt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeTransference.Poisson

open UpperTheory.V.Lit.Geo

theorem UpperTheory.geometric_side_estimate :
    ScaleFull := by
  unfold ScaleFull Scale
  intro V _ _ _ Λ _ _
  obtain ⟨hsum1, hsum2, c, hc, hP⟩ := PI.Tr.poissonGauss V Λ
  obtain ⟨α, hα⟩ : ∃ α : ℝ, α = (Module.finrank ℝ V : ℝ) / 2 := ⟨_, rfl⟩
  have e1 : -(Module.finrank ℝ V : ℝ) / 2 = -α := by rw [hα]; ring
  have key : ∀ r : ℝ, 0 < r → ∑' x : Λ, Real.exp (-Real.pi * (r * ‖(x : V)‖ ^ 2)) =
      c * r ^ (-α) * ∑' y : PI.Tr.dualLat Λ, Real.exp (-Real.pi * ‖(y : V)‖ ^ 2 / r) := by
    intro r hr
    have h := hP r hr 0
    simp only [add_zero, inner_zero_right, mul_zero, Real.cos_zero, mul_one] at h
    rw [← e1, ← h]
    refine tsum_congr (fun x => ?_)
    congr 1
    ring
  refine ⟨fun x => sq_nonneg _, fun s t hs hst => ?_⟩
  have ht : 0 < t := lt_of_lt_of_le hs hst
  refine ⟨by simpa [mul_assoc] using hsum1 s hs 0, ?_⟩
  rw [key s hs, key t ht]
  have hD : ∑' y : PI.Tr.dualLat Λ, Real.exp (-Real.pi * ‖(y : V)‖ ^ 2 / s) ≤
      ∑' y : PI.Tr.dualLat Λ, Real.exp (-Real.pi * ‖(y : V)‖ ^ 2 / t) := by
    refine Summable.tsum_le_tsum (fun y => Real.exp_le_exp.mpr ?_) (hsum2 s hs) (hsum2 t ht)
    have h0 : 0 ≤ Real.pi * ‖(y : V)‖ ^ 2 := by positivity
    have h3 : Real.pi * ‖(y : V)‖ ^ 2 / t ≤ Real.pi * ‖(y : V)‖ ^ 2 / s :=
      div_le_div_of_nonneg_left h0 hs hst
    rw [neg_mul, neg_div, neg_div]
    linarith
  have hD0 : 0 ≤ ∑' y : PI.Tr.dualLat Λ, Real.exp (-Real.pi * ‖(y : V)‖ ^ 2 / t) :=
    tsum_nonneg (fun y => (Real.exp_pos _).le)
  have hα0 : 0 ≤ α := by rw [hα]; positivity
  have hS : s ^ α ≤ t ^ α := Real.rpow_le_rpow hs.le hst hα0
  have hSpos : 0 < s ^ α := Real.rpow_pos_of_pos hs α
  have hTpos : 0 < t ^ α := Real.rpow_pos_of_pos ht α
  have hpow : (t / s) ^ Module.finrank ℝ V = (t ^ α) ^ 2 / (s ^ α) ^ 2 := by
    rw [← div_pow, ← Real.div_rpow ht.le hs.le, ← Real.rpow_mul_natCast (div_nonneg ht.le hs.le),
      ← Real.rpow_natCast]
    congr 1
    rw [hα]
    push_cast
    ring
  have hcD : 0 ≤ c * ∑' y : PI.Tr.dualLat Λ, Real.exp (-Real.pi * ‖(y : V)‖ ^ 2 / t) :=
    mul_nonneg hc.le hD0
  have h1 : (s ^ α)⁻¹ ≤ (t ^ α) ^ 2 / (s ^ α) ^ 2 * (t ^ α)⁻¹ := by
    rw [show (t ^ α) ^ 2 / (s ^ α) ^ 2 * (t ^ α)⁻¹ = t ^ α / (s ^ α) ^ 2 by
      field_simp]
    rw [inv_eq_one_div, div_le_div_iff₀ hSpos (by positivity)]
    nlinarith
  rw [Real.rpow_neg hs.le, Real.rpow_neg ht.le, hpow]
  calc c * (s ^ α)⁻¹ * ∑' y : PI.Tr.dualLat Λ, Real.exp (-Real.pi * ‖(y : V)‖ ^ 2 / s)
      ≤ c * (s ^ α)⁻¹ * ∑' y : PI.Tr.dualLat Λ, Real.exp (-Real.pi * ‖(y : V)‖ ^ 2 / t) :=
        mul_le_mul_of_nonneg_left hD (mul_nonneg hc.le (inv_nonneg.mpr hSpos.le))
    _ = (c * ∑' y : PI.Tr.dualLat Λ, Real.exp (-Real.pi * ‖(y : V)‖ ^ 2 / t)) * (s ^ α)⁻¹ := by ring
    _ ≤ (c * ∑' y : PI.Tr.dualLat Λ, Real.exp (-Real.pi * ‖(y : V)‖ ^ 2 / t)) *
          ((t ^ α) ^ 2 / (s ^ α) ^ 2 * (t ^ α)⁻¹) := mul_le_mul_of_nonneg_left h1 hcD
    _ = _ := by ring
