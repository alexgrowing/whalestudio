import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FlatDegree.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FlatTheorem

open NumberField

theorem FlatDegreeBound.one_le_rootDiscr (K : Type) [Field K] [NumberField K] :
    1 ≤ rootDiscr K := by
  rw [rootDiscr_def]
  have h : (1 : ℝ) ≤ ((|discr K| : ℤ) : ℝ) := by
    exact_mod_cast Int.one_le_abs (discr_ne_zero K)
  exact Real.one_le_rpow h (by positivity)

theorem FlatDegreeBound.rootDiscr_le_rootDiscr (K E : Type) [Field K] [NumberField K] [Field E]
    [NumberField E] [Algebra K E] : rootDiscr K ≤ rootDiscr E := by
  have key := natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow K (𝓞 K) E (𝓞 E)
  have hE0 : (discr E).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (discr_ne_zero E)
  have hN : Ideal.absNorm (differentIdeal (𝓞 K) (𝓞 E)) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at key
    exact hE0 key
  have hle : (discr K).natAbs ^ Module.finrank K E ≤ (discr E).natAbs := by
    rw [key]
    exact Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero hN)
  set n := Module.finrank ℚ K with hn
  set m := Module.finrank K E with hm
  have hnE : Module.finrank ℚ E = n * m := (Module.finrank_mul_finrank ℚ K E).symm
  have hnpos : 0 < n := Module.finrank_pos
  have hmpos : 0 < m := Module.finrank_pos
  have habsK : ((|discr K| : ℤ) : ℝ) = ((discr K).natAbs : ℝ) := (Nat.cast_natAbs _).symm
  have habsE : ((|discr E| : ℤ) : ℝ) = ((discr E).natAbs : ℝ) := (Nat.cast_natAbs _).symm
  rw [rootDiscr_def, rootDiscr_def, habsK, habsE, hnE]
  have hleR : (((discr K).natAbs : ℝ)) ^ (m : ℝ) ≤ ((discr E).natAbs : ℝ) := by
    rw [Real.rpow_natCast]
    exact_mod_cast hle
  have h0 : (0 : ℝ) ≤ ((discr K).natAbs : ℝ) := Nat.cast_nonneg _
  calc ((discr K).natAbs : ℝ) ^ (n : ℝ)⁻¹
      = (((discr K).natAbs : ℝ) ^ (m : ℝ)) ^ (((n * m : ℕ) : ℝ)⁻¹) := by
        rw [← Real.rpow_mul h0]
        congr 1
        push_cast
        field_simp
    _ ≤ ((discr E).natAbs : ℝ) ^ (((n * m : ℕ) : ℝ)⁻¹) :=
        Real.rpow_le_rpow (Real.rpow_nonneg h0 _) hleR (by positivity)

theorem FlatDegreeBound.proof : FlatDegreeBound.Statement := by
  intro K E _ _ _ _ _ p q logΩ c hc
  subst hc
  have h1 := FlatDegreeBound.one_le_rootDiscr K
  have h2 := FlatDegreeBound.rootDiscr_le_rootDiscr K E
  have hlK : 0 ≤ Real.log (rootDiscr K) := Real.log_nonneg h1
  have hlKE : Real.log (rootDiscr K) ≤ Real.log (rootDiscr E) :=
    Real.log_le_log (by linarith) h2
  have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have ha := mul_nonneg hq hlK
  have hb := mul_nonneg hq (sub_nonneg.mpr hlKE)
  rw [abs_le]
  constructor <;> nlinarith

end GroundTheory.Heights₂.Heights.FlatTheorem
