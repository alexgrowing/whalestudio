import Mathlib
import Development.DiscreteGroups.GlobalIrreducibility.DzNormV

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual

set_option linter.all false

noncomputable section

namespace DiscreteGroups.sglob.DzType

variable {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (g : ℕ) [hg : Fact g.Prime]

theorem g_not_mem_sq (i : ℚ_[g] ≃+* w.adicCompletion E) (hi : Continuous i) :
    ((g : ℕ) : 𝓞 E) ∉ w.asIdeal ^ 2 := by
  intro hg2
  have hvF : ∀ y : 𝓞 E, Valued.v (algebraMap E (w.adicCompletion E) (y : E)) = w.intValuation y := fun y => by
    have e : Valued.v (algebraMap E (w.adicCompletion E) (y : E)) = w.valuation E (y : E) :=
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (R := 𝓞 E) w (y : E)
    rw [e]; exact HeightOneSpectrum.valuation_of_algebraMap w y
  obtain ⟨π, hπ⟩ := w.intValuation_exists_uniformizer
  have hg2' : w.intValuation ((g : ℕ) : 𝓞 E) ≤ WithZero.exp (-(2 : ℕ) : ℤ) :=
    (w.intValuation_le_pow_iff_mem _ 2).mpr hg2
  set x := i.symm (algebraMap E (w.adicCompletion E) (π : E)) with hx
  have hxπ : i x = algebraMap E (w.adicCompletion E) (π : E) := by rw [hx, RingEquiv.apply_symm_apply]
  have hπ1 : Valued.v (algebraMap E (w.adicCompletion E) (π : E)) < 1 := by
    rw [hvF, hπ]
    have h0 : WithZero.exp (-1 : ℤ) < WithZero.exp 0 := WithZero.exp_lt_exp.mpr (by norm_num)
    simpa using h0
  have hxn : ‖x‖ < 1 := by
    rw [← DiscreteGroups.sglob.DzIso.norm_lt_iff i hi, hxπ, Valued.toNormedField.norm_lt_one_iff]
    exact hπ1
  have hxg : ‖x / (g : ℚ_[g])‖ ≤ 1 := by
    have h1 : ‖x‖ ≤ (g : ℝ) ^ (-1 : ℤ) := by
      rw [Padic.norm_le_pow_iff_norm_lt_pow_add_one]; simpa using hxn
    rw [norm_div, Padic.norm_p, div_le_one (inv_pos.mpr (by exact_mod_cast hg.out.pos))]
    simpa [zpow_neg, zpow_one] using h1
  have h2 := DiscreteGroups.sglob.DzIso.norm_le_of_le i hi hxg
  rw [Valued.toNormedField.norm_le_one_iff] at h2
  have e : algebraMap E (w.adicCompletion E) (π : E) = ((g : ℕ) : w.adicCompletion E) * i (x / (g : ℚ_[g])) := by
    rw [← hxπ, ← map_natCast i g, ← map_mul, mul_div_cancel₀]
    exact_mod_cast hg.out.ne_zero
  have h3 : Valued.v (algebraMap E (w.adicCompletion E) (π : E)) ≤ WithZero.exp (-(2 : ℕ) : ℤ) := by
    rw [e, map_mul]
    have hgv : Valued.v ((g : ℕ) : w.adicCompletion E) = w.intValuation ((g : ℕ) : 𝓞 E) := by
      rw [← hvF]; simp
    rw [hgv]
    calc w.intValuation ((g : ℕ) : 𝓞 E) * Valued.v (i (x / (g : ℚ_[g])))
        ≤ w.intValuation ((g : ℕ) : 𝓞 E) * 1 := mul_le_mul_right h2 _
      _ ≤ _ := by rw [mul_one]; exact hg2'
  rw [hvF, hπ, WithZero.exp_le_exp] at h3
  norm_num at h3

end DiscreteGroups.sglob.DzType

end
