import Formalism.HermitianCurvature.StatementL

namespace Formalism.FourierDecayAlt.P.Dual

open NumberField FractionalIdeal

theorem alg {E : Type} [Field E] [NumberField E] (dd : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)
    (hdd : dd ≠ 0) (ν g : ℤ) (hg : g ≠ 0) :
    spanSingleton _ (g : E) * (dd⁻¹ * (dd ^ ν * spanSingleton _ ((g : E) ^ 2))⁻¹) =
      dd ^ (-(ν + 1)) * spanSingleton _ ((g : E)⁻¹) := by
  have hgE : (g : E) ≠ 0 := by exact_mod_cast hg
  rw [mul_inv (dd ^ ν), spanSingleton_inv]
  have h1 : spanSingleton (nonZeroDivisors (𝓞 E)) (g : E) * spanSingleton _ (((g : E) ^ 2)⁻¹) =
      spanSingleton _ ((g : E)⁻¹) := by
    rw [spanSingleton_mul_spanSingleton]; congr 1; field_simp
  rw [show dd ^ (-(ν + 1)) = dd⁻¹ * (dd ^ ν)⁻¹ by
    rw [neg_add, zpow_add₀ hdd, _root_.zpow_neg, zpow_neg_one, mul_comm]]
  rw [← h1]; ring

theorem dual_ideal_inclusion : Formalism.FourierDecayAlt.L.DualIdealInclusion := by
  intro E _ _ dd h1 ν g hg La hLa
  have hdd : dd ≠ 0 := by
    intro h0; rw [h0, _root_.inv_zero] at h1; exact dual_ne_zero ℤ ℚ (one_ne_zero (α := FractionalIdeal (nonZeroDivisors (𝓞 E)) E)) h1
  have hgE : (g : E) ≠ 0 := by exact_mod_cast hg
  have hJ : dd ^ ν * spanSingleton (nonZeroDivisors (𝓞 E)) ((g : E) ^ 2) ≠ 0 :=
    mul_ne_zero (zpow_ne_zero _ hdd) (by simp [spanSingleton_eq_zero_iff, hgE])
  have hLa0 : La ≠ 0 := fun h => hJ (le_antisymm (by simpa [h] using hLa) (FractionalIdeal.zero_le _))
  have hd := (dual_le_dual ℤ ℚ hLa0 hJ).mpr hLa
  rw [dual_eq_mul_inv ℤ ℚ (dd ^ ν * spanSingleton _ ((g : E) ^ 2)), h1] at hd
  calc spanSingleton _ (g : E) * dual ℤ ℚ La
      ≤ spanSingleton _ (g : E) * (dd⁻¹ * (dd ^ ν * spanSingleton _ ((g : E) ^ 2))⁻¹) :=
        mul_le_mul_right hd _
    _ = _ := alg dd hdd ν g hg

theorem dual_third_group_integral : Formalism.FourierDecayAlt.L.DualLatticeInclusion := by
  intro E _ _ dd h1 ν g hg La hLa x hx
  have hdd : dd ≠ 0 := by
    intro h0; rw [h0, _root_.inv_zero] at h1; exact dual_ne_zero ℤ ℚ (one_ne_zero (α := FractionalIdeal (nonZeroDivisors (𝓞 E)) E)) h1
  have hgE : (g : E) ≠ 0 := by exact_mod_cast hg
  have hJ : dd ^ ν * spanSingleton (nonZeroDivisors (𝓞 E)) ((g : E) ^ 2) ≠ 0 :=
    mul_ne_zero (zpow_ne_zero _ hdd) (by simp [spanSingleton_eq_zero_iff, hgE])
  have hy : x * (g : E)⁻¹ ∈ dual ℤ ℚ (dd ^ ν * spanSingleton _ ((g : E) ^ 2)) := by
    rw [mem_dual hJ]
    intro a ha
    have := hx a (hLa a ha)
    rw [Algebra.traceForm_apply]
    convert this using 2
    field_simp
  rw [dual_eq_mul_inv ℤ ℚ, h1] at hy
  rw [← alg dd hdd ν g hg]
  have := mul_mem_mul (mem_spanSingleton_self (nonZeroDivisors (𝓞 E)) (g : E)) hy
  convert this using 1
  field_simp

end Formalism.FourierDecayAlt.P.Dual

theorem Formalism.FourierDecayAlt.P.dual_third_group_holds : Formalism.FourierDecayAlt.L.DualLatticeInclusion := Formalism.FourierDecayAlt.P.Dual.dual_third_group_integral
theorem Formalism.FourierDecayAlt.P.dual_third_group_ideal : Formalism.FourierDecayAlt.L.DualIdealInclusion := Formalism.FourierDecayAlt.P.Dual.dual_ideal_inclusion
