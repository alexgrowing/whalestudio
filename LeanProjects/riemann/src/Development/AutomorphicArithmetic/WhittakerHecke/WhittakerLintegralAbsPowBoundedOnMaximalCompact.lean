import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.Aa
import Development.AutomorphicArithmetic.WhittakerHecke.LintegralIdeleRatPolyDecayMulNormRpowLtTop
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.KkCpt
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical ENNReal NNReal
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)

theorem UpperTheory.whittaker_lintegral_abs_pow_bounded_on_maximalCompact :
    ∀ (E : Type) [Field E] [NumberField E] (D : Dat ℚ E) (ω : HChar ℚ) (φ : GL (Fin 2) (A E) → ℂ), admitted D ω φ → ∀ x : ℝ, 1 < x → ∃ C : ℝ≥0, ∀ k ∈ KK ℚ,
        ∫⁻ y : IdeleGroup ℚ, ‖Wo D φ (em E (aE y * gl k))‖ₑ * ENNReal.ofReal (ab y ^ x) ∂(ideleMeasure ℚ) ≤ C := by
  intro E _ _ D ω φ hA x hx
  have hemc : Continuous (em E) :=
    Continuous.units_map _ (Continuous.matrix_map continuous_id AdeleBaseChange.continuous_adeleMap)
  have hglc : Continuous (gl : G1 ℚ → GL (Fin 2) (A ℚ)) := Matrix.SpecialLinearGroup.continuous_toGL
  have hC : IsCompact ((fun k : G1 ℚ => em E (gl k)) '' KK ℚ) :=
    (UpperTheory.ConvolutionTheory.R2.M.kkCpt ℚ).2.image (hemc.comp hglc)
  obtain ⟨K, hKc, hK⟩ := hA.wdec _ hC
  obtain ⟨r, hr⟩ := exists_nat_gt x
  obtain ⟨B, hB⟩ := hK r
  have hI := UpperTheory.lintegral_idele_rat_polyDecay_mul_norm_rpow_lt_top K hKc x hx r hr
  refine ⟨(ENNReal.ofReal |B| * ∫⁻ y : IdeleGroup ℚ, (if (y : A ℚ).2 ∈ K then ENNReal.ofReal (((1 + |re (y : A ℚ)|) ^ r)⁻¹ * ab y ^ x) else 0) ∂(ideleMeasure ℚ)).toNNReal, fun k hk => ?_⟩
  rw [ENNReal.coe_toNNReal (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hI.ne),
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun y => ?_
  have hb := hB y (em E (gl k)) ⟨k, hk, rfl⟩
  rw [← map_mul] at hb
  have hab : 0 ≤ ab y ^ x := Real.rpow_nonneg (IdeleGroup.ideleModule ℚ y).2.le x
  by_cases hy : (y : A ℚ).2 ∈ K
  · rw [if_pos hy, ← ENNReal.ofReal_mul (abs_nonneg _), ← ofReal_norm_eq_enorm,
      ← ENNReal.ofReal_mul (norm_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [← mul_assoc]
    refine mul_le_mul_of_nonneg_right (hb.1.trans ?_) hab
    exact mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
  · have h0 : Wo D φ (em E (aE y * gl k)) = 0 := by
      by_contra h
      exact hy (hb.2 h)
    rw [h0, enorm_zero, zero_mul]
    exact bot_le
