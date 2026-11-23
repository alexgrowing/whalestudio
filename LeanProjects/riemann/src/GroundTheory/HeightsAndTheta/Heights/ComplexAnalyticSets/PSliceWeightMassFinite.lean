import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceWeightMassFinite
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSheetSumMeasurable
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCutOffGradient
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets

noncomputable section

theorem SliceWeightMassFinite.exists_bound {n : ℕ} (a : (Fin n → ℂ) → ℝ)
    (hdeg : ∀ (t : ℂ) (x : Fin n → ℂ), t ≠ 0 → a (t • x) = a x) (ha : ContinuousOn a {x | x ≠ 0}) :
    ∃ M : ℝ, ∀ x : Fin n → ℂ, x ≠ 0 → |a x| ≤ M := by
  obtain ⟨M, hM⟩ := (isCompact_sphere (0 : Fin n → ℂ) 1).exists_bound_of_continuousOn
    (ha.mono fun x hx h0 => by simp [h0] at hx)
  refine ⟨M, fun x hx => ?_⟩
  have hx' : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hn : ((‖x‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hx'
  rw [← hdeg (((‖x‖ : ℝ) : ℂ))⁻¹ x (inv_ne_zero hn), ← Real.norm_eq_abs]
  refine hM _ ?_
  rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, Complex.norm_real, norm_norm, inv_mul_cancel₀ hx']

theorem SliceWeightMassFinite.proof (h₁ : SliceMassFinite.Statement) : SliceWeightMassFinite.Statement := by
  classical
  intro n d h I ℓ A a hI hℓ hdim hA hdeg ha
  set φ : Fin d → (Fin n → ℂ) → ℝ := fun _ x => Real.log (h.dualNorm x) with hφ
  have h0 : ∀ x ∈ zeroSet I, x ≠ 0 := by
    rintro x hx rfl
    have := hx _ hℓ
    simp [linForm] at this
  obtain ⟨M, hM⟩ := SliceWeightMassFinite.exists_bound a hdeg ha
  set g : (Fin n → ℂ) → ℝ := (zeroSet I).piecewise a 0 with hgdef
  have hg : Measurable g :=
    (ha.mono fun x hx => h0 x hx).measurable_piecewise continuousOn_const
      (SheetSumMeasurable.isClosed_zeroSet I).measurableSet
  have heq : chartAbsDens I A a φ = chartAbsDens I A g φ := by
    funext y
    unfold chartAbsDens sheetSum
    refine finsum_congr fun x => finsum_congr fun hx => ?_
    simp only [hgdef, Set.piecewise_eq_of_mem _ _ _ hx.1]
  have hmeas : Measurable (chartAbsDens I A a φ) := by
    rw [heq]
    exact SheetSumMeasurable.measurable_sheetSum hA (fun u v => |u * v|)
      (continuous_fst.mul continuous_snd).abs.measurable hg φ
  refine ((h₁ n d h I ℓ A hI hℓ hdim hA).const_mul M).mono' hmeas.aestronglyMeasurable
    (Eventually.of_forall fun y => ?_)
  have hnn : 0 ≤ chartAbsDens I A a φ y :=
    finsum_nonneg fun _ => finsum_nonneg fun _ => by split_ifs <;> positivity
  rw [Real.norm_eq_abs, abs_of_nonneg hnn]
  refine sheetSum_le_mul (IndefiniteRowSideFullHecke.ComplexSets.fibre_finite hA y) M _ _ fun x hx s _ => ?_
  rw [abs_mul, one_mul]
  exact mul_le_mul_of_nonneg_right (hM x (h0 x hx.1)) (abs_nonneg _)

end

end GroundTheory.Heights₂.Heights
