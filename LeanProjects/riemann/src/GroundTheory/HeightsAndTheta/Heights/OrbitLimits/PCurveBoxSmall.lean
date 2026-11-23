import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsCurveBoxSmall
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.CurveOrbitEmbedding
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.Inter

theorem CurveBoxSmall.zpow_mul_toNat_neg {F : Type} [Field F] {t : F} (ht : t ≠ 0) (n : ℤ) :
    t ^ n * t ^ (-n).toNat = t ^ n.toNat :=
  calc t ^ n * t ^ (-n).toNat = t ^ ((n.toNat : ℤ) - ((-n).toNat : ℤ)) * t ^ (-n).toNat := by
        rw [Int.toNat_sub_toNat_neg]
    _ = t ^ n.toNat := by
        rw [zpow_sub₀ ht, zpow_natCast, zpow_natCast, div_mul_cancel₀ _ (pow_ne_zero _ ht)]

theorem CurveBoxSmall.proof : CurveBoxSmall.Statement := by
  intro K _ ι _ Ω _ y A c hP hB hc τ s
  classical
  have hU : ∀ σ : Ω →+* ℂ, ‖σ (chartUnit y c A.a τ)‖ = (∏ k, ‖σ (y ⟨k, c k⟩)‖ ^ A.a k) ^ τ := fun σ => by
    rw [chartUnit, map_prod, norm_prod, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [map_zpow₀, norm_zpow, ← zpow_natCast (_ ^ A.a k), ← zpow_mul, mul_comm (A.a k)]
  have hQ : ∀ σ : Ω →+* ℂ, 0 < (∏ k, ‖σ (y ⟨k, c k⟩)‖ ^ A.a k) ^ τ := fun σ =>
    pow_pos (Finset.prod_pos fun k _ => zpow_pos (norm_pos_iff.mpr ((map_ne_zero σ).mpr (hc k))) _) _
  constructor
  · intro hS σ
    obtain ⟨d, g, h, hg, hh, hh0, hgh⟩ := hB (s / chartUnit y c A.a τ)
    let ap : K → ℕ := fun k => ((τ : ℤ) * A.a k).toNat
    let am : K → ℕ := fun k => (-((τ : ℤ) * A.a k)).toNat
    have hU0 : chartUnit y c A.a τ ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (hc k)
    have hu : chartUnit y c A.a τ * ∏ k, y ⟨k, c k⟩ ^ am k = ∏ k, y ⟨k, c k⟩ ^ ap k := by
      rw [chartUnit, ← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun k _ => CurveBoxSmall.zpow_mul_toNat_neg (hc k) _
    have hdeg : ∀ k, (((d + ap) k : ℕ) : ℤ) = ((d + am) k : ℕ) + τ * A.a k := fun k => by
      have := Int.toNat_sub_toNat_neg ((τ : ℤ) * A.a k)
      simp only [Pi.add_apply, Nat.cast_add, ap, am]
      omega
    have hval : aeval y (g * curveChartMono c ap) = s * aeval y (h * curveChartMono c am) := by
      simp only [map_mul, curveChartMono, map_prod, map_pow, aeval_X]
      rw [← hu, hgh]
      field_simp
    have hS' := hS _ _ _ _ _ (CurveOrbit.isMultiHomog_mul hg (isMultiHomog_curveChartMono c ap))
      (CurveOrbit.isMultiHomog_mul hh (isMultiHomog_curveChartMono c am)) hdeg hval (CurveOrbit.mem_mcPts σ y hc)
    rw [CurveOrbit.eval_comp, CurveOrbit.eval_comp] at hS'
    simp only [map_mul, curveChartMono, map_prod, map_pow, aeval_X, norm_mul, norm_prod, norm_pow] at hS'
    have hsu : s / chartUnit y c A.a τ = aeval y g / aeval y h := eq_div_of_mul_eq hh0 hgh.symm
    have hσh : 0 < ‖σ (aeval y h)‖ := norm_pos_iff.mpr ((map_ne_zero σ).mpr hh0)
    have ht : ∀ k, ‖σ (y ⟨k, c k⟩)‖ ≠ 0 := fun k => norm_ne_zero_iff.mpr ((map_ne_zero σ).mpr (hc k))
    have hR : (∏ k, ‖σ (y ⟨k, c k⟩)‖ ^ A.a k) ^ τ * ∏ k, ‖σ (y ⟨k, c k⟩)‖ ^ am k =
        ∏ k, ‖σ (y ⟨k, c k⟩)‖ ^ ap k := by
      rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [← zpow_natCast (_ ^ A.a k), ← zpow_mul, mul_comm (A.a k)]
      exact CurveBoxSmall.zpow_mul_toNat_neg (ht k) _
    have hRm : 0 < ∏ k, ‖σ (y ⟨k, c k⟩)‖ ^ am k :=
      Finset.prod_pos fun k _ => pow_pos (lt_of_le_of_ne (norm_nonneg _) (ht k).symm) _
    rw [hsu, map_div₀, norm_div, chartRadius, div_pow, div_le_div_iff₀ hσh (hQ σ)]
    refine le_of_mul_le_mul_right ?_ hRm
    calc ‖σ (aeval y g)‖ * (∏ k, ‖σ (y ⟨k, c k⟩)‖ ^ A.a k) ^ τ * ∏ k, ‖σ (y ⟨k, c k⟩)‖ ^ am k
        = ‖σ (aeval y g)‖ * ∏ k, ‖σ (y ⟨k, c k⟩)‖ ^ ap k := by rw [mul_assoc, hR]
      _ ≤ ‖σ (aeval y h)‖ * (∏ k, ‖σ (y ⟨k, c k⟩)‖ ^ am k) * A.h (fun p => σ (y p)) ^ τ := hS'
      _ = _ := by ring
  · intro hbox dg dh g h z hg hh hdeg hgs hz
    obtain ⟨σ, l, hl, rfl⟩ := CurveOrbit.exists_sameOrbit hP hB hz
    beta_reduce
    have hb := hbox σ
    rw [map_div₀, norm_div, chartRadius, div_pow, hU σ, div_le_div_iff_of_pos_right (hQ σ)] at hb
    have hlam : ‖∏ k, l k ^ dg k‖ = ‖∏ k, l k ^ dh k‖ * (∏ k, ‖l k‖ ^ A.a k) ^ τ := by
      rw [norm_prod, norm_prod, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      have hlk : ‖l k‖ ≠ 0 := norm_ne_zero_iff.mpr (hl k)
      rw [norm_pow, norm_pow, ← zpow_natCast (‖l k‖) (dg k), hdeg k, zpow_add₀ hlk, zpow_natCast,
        ← zpow_natCast (_ ^ A.a k), ← zpow_mul, mul_comm (A.a k)]
    rw [CurveOrbit.eval_smul _ l hg, CurveOrbit.eval_smul _ l hh, A.smul l _ hl, CurveOrbit.eval_comp,
      CurveOrbit.eval_comp, hgs, map_mul, norm_mul, norm_mul, norm_mul, hlam, mul_pow]
    calc ‖∏ k, l k ^ dh k‖ * (∏ k, ‖l k‖ ^ A.a k) ^ τ * (‖σ s‖ * ‖σ (aeval y h)‖)
        = (‖∏ k, l k ^ dh k‖ * (∏ k, ‖l k‖ ^ A.a k) ^ τ * ‖σ (aeval y h)‖) * ‖σ s‖ := by ring
      _ ≤ (‖∏ k, l k ^ dh k‖ * (∏ k, ‖l k‖ ^ A.a k) ^ τ * ‖σ (aeval y h)‖) * A.h (fun p => σ (y p)) ^ τ :=
        mul_le_mul_of_nonneg_left hb (by positivity)
      _ = _ := by ring

end GroundTheory.Heights₂.Heights.Targets
