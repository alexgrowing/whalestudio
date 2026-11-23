import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.GoodModelAll
import Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.CmAll
import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.NonsingularJetNorms.CmIntegralityOfTorsionPoints
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.EllipticOnePole
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModJInt

noncomputable section

namespace Formalism.L2.Th1.Top

open Formalism.L2.Th1.CM (HasCMBy jInv)
open Formalism.L2.Th1.E (IntCurve curveL)

namespace GM

variable (p : ℕ) [Fact p.Prime]

theorem norm_divisor_twelve_power_eq_one (h5 : 5 ≤ p) {N k : ℕ} (hN : N ∣ 12 ^ k) : ‖(N : ℂ_[p])‖ = 1 := by
  refine Formalism.L2.Th1.E.ScaledModelNorms.norm_nat p fun h => ?_
  have hp : p.Prime := Fact.out
  have h12 : p ∣ 12 := hp.dvd_of_dvd_pow (h.trans hN)
  have hle : p ≤ 12 := Nat.le_of_dvd (by norm_num) h12
  interval_cases p <;> first | omega | exact absurd hp (by norm_num)

theorem norm_twelve_cubed_eq_one_of_five_le_prime (h5 : 5 ≤ p) : ‖(1728 : ℂ_[p])‖ = 1 := by
  have := norm_divisor_twelve_power_eq_one p h5 (N := 1728) (k := 3) (by norm_num)
  simpa using this

theorem norm_27 (h5 : 5 ≤ p) : ‖(27 : ℂ_[p])‖ = 1 := by
  have := norm_divisor_twelve_power_eq_one p h5 (N := 27) (k := 3) (by norm_num)
  simpa using this

end GM

theorem good_model_exists_all_primes : GoodModelAll := by
  intro dK L hsq hd4 hcm p _ h5 ι
  have hD0 : L.g₂ ^ 3 - 27 * L.g₃ ^ 2 ≠ 0 := Formalism.L2.Th1.F.discNeZero L
  obtain ⟨c, hc12⟩ := IsAlgClosed.exists_pow_nat_eq (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) (show 0 < 12 by norm_num)
  have hc : c ≠ 0 := by
    intro h
    rw [h] at hc12
    exact hD0 (by rw [← hc12]; simp)
  refine ⟨c, hc, ?_⟩
  have hH := Formalism.L2.Th1.F.homogeneity L c hc
  have e2 : (Formalism.L2.Th1.F.scalePair L c hc).g₂ = (c ^ 4)⁻¹ * L.g₂ := hH.2.2.2.2.2.2.2.2.2.1
  have e3 : (Formalism.L2.Th1.F.scalePair L c hc).g₃ = (c ^ 6)⁻¹ * L.g₃ := hH.2.2.2.2.2.2.2.2.2.2
  set a : ℂ := (Formalism.L2.Th1.F.scalePair L c hc).g₂ with ha
  set b : ℂ := (Formalism.L2.Th1.F.scalePair L c hc).g₃ with hb

  have hΔ : a ^ 3 - 27 * b ^ 2 = 1 := by
    rw [e2, e3]
    have : ((c ^ 4)⁻¹ * L.g₂) ^ 3 - 27 * ((c ^ 6)⁻¹ * L.g₃) ^ 2 =
        (c ^ 12)⁻¹ * (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) := by
      field_simp
    rw [this, hc12, inv_mul_cancel₀ hD0]
  have hj : 1728 * a ^ 3 = jInv L := by
    unfold jInv
    rw [e2, ← hc12]
    field_simp
  have hJ : ‖ι (jInv L)‖ ≤ 1 :=
    ReciprocityTheory.ChartRestriction.L1.jInt dK L hsq hd4 hcm p ι
  have ha3 : ‖ι a‖ ^ 3 ≤ 1 := by
    have h := congrArg ι hj
    rw [map_mul, map_pow, map_ofNat] at h
    rw [← h, norm_mul, GM.norm_twelve_cubed_eq_one_of_five_le_prime p h5, one_mul, norm_pow] at hJ
    exact hJ
  have ha1 : ‖ι a‖ ≤ 1 := (pow_le_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).1 ha3
  have hb2 : ‖ι b‖ ^ 2 ≤ 1 := by
    have h : 27 * ι b ^ 2 = ι a ^ 3 - 1 := by
      have h := congrArg ι hΔ
      rw [map_sub, map_mul, map_pow, map_pow, map_ofNat, map_one] at h
      linear_combination -h
    have h' := congrArg norm h
    rw [norm_mul, GM.norm_27 p h5, one_mul, norm_pow] at h'
    rw [h', sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ (by simp))
    rw [norm_pow]; exact ha3
  have hb1 : ‖ι b‖ ≤ 1 := (pow_le_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).1 hb2
  unfold curveL
  refine Formalism.L2.Th1.E.ScaledModelNorms.intCurve_short p h5 _ _ ha1 hb1 ?_
  have h := congrArg ι hΔ
  rw [map_sub, map_mul, map_pow, map_pow, map_ofNat, map_one] at h
  rw [h, norm_one]

end Formalism.L2.Th1.Top
