import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.BlockMinorSumCounterexample

open MeasureTheory Finset
open scoped ENNReal

namespace GlobalTheory.MomentHolder

theorem lintegral_density {Ω : Type} [MeasurableSpace Ω] (ν : Measure Ω) (Ph : Ω → ℝ)
    (hPh : AEMeasurable Ph ν) (h0 : ∀ x, 0 ≤ Ph x) (f : Ω → ℝ) (hf : Measurable f) :
    ∫⁻ x, ENNReal.ofReal (f x) ∂(ν.withDensity fun x => ENNReal.ofReal (Ph x))
      = ∫⁻ x, ENNReal.ofReal (f x * Ph x) ∂ν := by
  rw [lintegral_withDensity_eq_lintegral_mul₀ hPh.ennreal_ofReal
    hf.ennreal_ofReal.aemeasurable]
  refine lintegral_congr fun x => ?_
  simp only [Pi.mul_apply]
  rw [mul_comm (f x), ENNReal.ofReal_mul (h0 x)]

theorem exists_pos_version {Ω : Type} [MeasurableSpace Ω] (ν : Measure Ω) (f : Ω → ℝ)
    (hf : AEMeasurable f ν) (hpos : ∀ᵐ x ∂ν, 0 < f x) :
    ∃ g : Ω → ℝ, Measurable g ∧ (∀ x, 0 < g x) ∧ f =ᵐ[ν] g := by
  classical
  refine ⟨fun x => if 0 < hf.mk f x then hf.mk f x else 1, ?_, ?_, ?_⟩
  · exact Measurable.ite (measurableSet_lt measurable_const hf.measurable_mk)
      hf.measurable_mk measurable_const
  · intro x
    by_cases h : 0 < hf.mk f x <;> simp [h]
  · filter_upwards [hf.ae_eq_mk, hpos] with x hx hp
    rw [← hx, if_pos hp]

theorem product_moment_le :
    ∀ (Ω : Type) [MeasurableSpace Ω] (ν : Measure Ω) (r : ℕ) (len : Fin (r + 1) → Ω → ℝ)
      (Ph : Ω → ℝ) (A Rr : ℝ), (∀ a, AEMeasurable (len a) ν) → (∀ a, ∀ᵐ x ∂ν, 0 < len a x) →
      AEMeasurable Ph ν → (∀ x, 0 ≤ Ph x) → ∫⁻ x, ENNReal.ofReal (Ph x) ∂ν = 1 → 0 ≤ A → 1 ≤ Rr →
      (∀ q ≤ (r + 1) ^ 2, ∫⁻ x, ENNReal.ofReal (len 0 x ^ (2 * q) * Ph x) ∂ν
        ≤ ENNReal.ofReal (A ^ q)) →
      (∀ a : Fin r, ∀ q ≤ (r + 1) ^ 2,
        ∫⁻ x, ENNReal.ofReal ((len a.succ x / len a.castSucc x) ^ (2 * q) * Ph x) ∂ν
          ≤ ENNReal.ofReal (Rr ^ (2 * q))) →
      ∫⁻ x, ENNReal.ofReal ((∏ a, len a x ^ 2) * Ph x) ∂ν
        ≤ ENNReal.ofReal ((A * Rr ^ (2 * r)) ^ (r + 1)) := by
  intro Ω _ ν r len Ph A Rr hm hpos hPh h0 hmass hA hR h1 h2
  choose l hlm hlp hle using fun a => exists_pos_version ν (len a) (hm a) (hpos a)
  have hall : ∀ᵐ x ∂ν, ∀ a, len a x = l a x := ae_all_iff.2 hle
  set μ : Measure Ω := ν.withDensity fun x => ENNReal.ofReal (Ph x) with hμ
  haveI : IsProbabilityMeasure μ := ⟨by
    rw [hμ, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, hmass]⟩
  have hR0 : 0 ≤ Rr := zero_le_one.trans hR
  have hsq : ∀ q : ℕ, Real.sqrt A ^ (2 * q) = A ^ q := fun q => by
    rw [pow_mul, Real.sq_sqrt hA]
  have hup := Formalism.HermitianLatticeCounting.P.corollary_upper_estimate_holds Ω μ r (r + 1) l (Real.sqrt A) Rr hlm hlp
    (Real.sqrt_nonneg A) hR0
    (fun q hq => by
      rw [hμ, lintegral_density ν Ph hPh h0 _ ((hlm 0).pow_const _), hsq]
      refine le_of_eq_of_le (lintegral_congr_ae ?_) (h1 q (by rw [sq]; exact hq))
      filter_upwards [hall] with x hx
      rw [hx])
    (fun c q hq => by
      rw [hμ, lintegral_density ν Ph hPh h0
        (fun ω => (l c.succ ω / l c.castSucc ω) ^ (2 * q)) (((hlm _).div (hlm _)).pow_const _)]
      refine le_of_eq_of_le (lintegral_congr_ae ?_) (h2 c q (by rw [sq]; exact hq))
      filter_upwards [hall] with x hx
      rw [hx, hx])
  have hprod := Formalism.HermitianLatticeCounting.P.corollary_product_estimate_holds Ω μ r 1 (r + 1) l (Real.sqrt A * Rr ^ r) hlm hlp
    (by positivity) le_rfl
    (fun a _ => by
      rw [mul_one]
      refine (hup a).trans (ENNReal.ofReal_le_ofReal ?_)
      rw [mul_pow, ← pow_mul Rr r]
      refine mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hR ?_) (by positivity)
      rw [mul_comm r]
      exact Nat.mul_le_mul_left _ (Nat.lt_succ_iff.1 a.isLt))
  have hfilt : univ.filter (fun a : Fin (r + 1) => a.val < r + 1) = univ :=
    filter_true_of_mem fun a _ => a.isLt
  rw [hfilt, hμ, lintegral_density ν Ph hPh h0 _
    ((Finset.measurable_prod _ fun a _ => hlm a).pow_const _)] at hprod
  refine le_of_eq_of_le (lintegral_congr_ae ?_) (hprod.trans_eq ?_)
  · filter_upwards [hall] with x hx
    simp only [hx, mul_one, Finset.prod_pow]
  · congr 1
    rw [mul_one, mul_pow, hsq, mul_pow, ← pow_mul, ← pow_mul]
    congr 2
    ring

end GlobalTheory.MomentHolder
