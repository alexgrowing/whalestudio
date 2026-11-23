import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AmpleOnAbelianBase
import Development.AutomorphicArithmetic.CyclotomicBounds.TraceDuality.ValGen
open NumberField
open scoped NNReal

theorem UpperTheory.WildB.normGen :
    ∀ (E : Type) [Field E] [NumberField E] [IsGalois ℚ E] (p : ℕ) [Fact p.Prime] (d : 𝓞 E) (m : ℕ), d ∈ differentIdeal ℤ (𝓞 E) → ¬ p ∣ m → (∀ a ∈ differentIdeal ℤ (𝓞 E), d ∣ (m : 𝓞 E) * a) → ∀ φ : E →+* ℂ_[p], Real.log ‖φ (d : E)‖ = -(GlobalTheory.ShFam.Pad.vDiff E p * Real.log p) := by
  intro E _ _ _ p hp d m hd hm hdiv φ
  have hnp : ‖(p : ℂ_[p])‖ = (p : ℝ)⁻¹ := by
    rw [← map_natCast (algebraMap ℚ_[p] ℂ_[p]) p, norm_algebraMap', Padic.norm_p]
  let v : Valuation ℂ_[p] ℝ≥0 := NormedField.valuation
  have hv : ∀ x, ((v x : ℝ≥0) : ℝ) = ‖x‖ := fun x => rfl
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.1.one_lt
  have hlt : v (p : ℂ_[p]) < 1 := by
    rw [← NNReal.coe_lt_coe, hv, hnp, NNReal.coe_one]
    exact inv_lt_one_of_one_lt₀ hp1
  have h := UpperTheory.WildB.valGen E p hp.1 d m hd hm hdiv ℂ_[p] v hlt φ
  have h2 := congrArg (fun x : ℝ≥0 => Real.log (x : ℝ)) h
  simp only [NNReal.coe_pow, hv, hnp, Real.log_pow, Real.log_inv] at h2
  have hn : (Module.finrank ℚ E : ℝ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ℚ) (M := E)).ne'
  unfold GlobalTheory.ShFam.Pad.vDiff
  field_simp
  linarith
