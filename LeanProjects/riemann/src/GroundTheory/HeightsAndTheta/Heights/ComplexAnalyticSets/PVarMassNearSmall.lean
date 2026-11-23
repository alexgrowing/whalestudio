import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StVarMassNearSmall
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StChartMassCompact
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsArea
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PFibreBound
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSheetSumMeasurable
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PNullSmaller
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ENNReal NNReal

noncomputable section

namespace VarMassNearSmall

variable {n d : ℕ}

theorem abs_sheetSum_le (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    {F G : (Fin n → ℂ) → ((Fin d → ℂ) → Fin n → ℂ) → ℝ} (hFG : ∀ x s, |F x s| ≤ G x s)
    {y : Fin d → ℂ} (hfin : (fibre J A y).Finite) :
    |sheetSum J A F y| ≤ sheetSum J A G y := by
  classical
  unfold sheetSum
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, finsum_mem_eq_finite_toFinset_sum _ hfin]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x _ => ?_)
  split_ifs with h
  · exact hFG x _
  · simp

theorem volume_eq_zero_of_hausdorff {S : Set (Fin d → ℂ)} (hS : μH[((2 * d : ℕ) : ℝ)] S = 0) :
    volume S = 0 := by
  let E : ((Σ _ : Fin d, Fin 2) → ℝ) ≃L[ℝ] (Fin d → ℂ) :=
    (Pi.basis (fun _ : Fin d => Complex.basisOneI)).equivFun.symm.toContinuousLinearEquiv
  have hcard : Fintype.card (Σ _ : Fin d, Fin 2) = 2 * d := by
    simp [Fintype.card_sigma, mul_comm]
  have hT : volume (E ⁻¹' S) = 0 := by
    rw [← hausdorffMeasure_pi_real, hcard]
    have h := E.symm.lipschitz.hausdorffMeasure_image_le (d := ((2 * d : ℕ) : ℝ)) (by positivity) S
    rw [hS, mul_zero, nonpos_iff_eq_zero, ContinuousLinearEquiv.image_symm_eq_preimage] at h
    exact h
  have : (Measure.map E volume).IsAddHaarMeasure := E.isAddHaarMeasure_map volume
  have hac : (volume : Measure (Fin d → ℂ)) ≪ Measure.map E volume :=
    Measure.absolutelyContinuous_isAddHaarMeasure _ _
  apply hac
  exact (E.toHomeomorph.toMeasurableEquiv.map_apply S).trans hT

theorem volume_image_eq_zero (W I : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (hI : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ I) < d) :
    volume (A.mulVec '' (zeroSet W ∩ zeroSet I)) = 0 := by
  have hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ (W ⊔ I)) < d :=
    (ringKrullDim_le_of_surjective _ (Ideal.Quotient.factor_surjective le_sup_right)).trans_lt hI
  have h0 := NullSmaller.proof n d (W ⊔ I) hdim
  let L : EuclideanSpace ℂ (Fin n) →L[ℂ] (Fin d → ℂ) :=
    (Matrix.mulVecLin A).toContinuousLinearMap.comp (EuclideanSpace.equiv (Fin n) ℂ).toContinuousLinearMap
  have hsub : A.mulVec '' (zeroSet W ∩ zeroSet I) ⊆ L '' zeroSetEuc (W ⊔ I) := by
    rintro _ ⟨x, ⟨hxW, hxI⟩, rfl⟩
    refine ⟨(EuclideanSpace.equiv (Fin n) ℂ).symm x, fun q hq => ?_, by simp only [L, ContinuousLinearMap.comp_apply]; rfl⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hq
    have hx : (fun i => ((EuclideanSpace.equiv (Fin n) ℂ).symm x) i) = x := rfl
    rw [hx, map_add, hxW a ha, hxI b hb, add_zero]
  refine volume_eq_zero_of_hausdorff (le_antisymm ?_ bot_le)
  calc μH[((2 * d : ℕ) : ℝ)] (A.mulVec '' (zeroSet W ∩ zeroSet I))
      ≤ μH[((2 * d : ℕ) : ℝ)] (L '' zeroSetEuc (W ⊔ I)) := measure_mono hsub
    _ ≤ _ := L.lipschitz.hausdorffMeasure_image_le (by positivity) _
    _ = 0 := by rw [h0, mul_zero]

end VarMassNearSmall

open VarMassNearSmall in

theorem VarMassNearSmall.proof (hCMC : ChartMassCompact.Statement) : VarMassNearSmall.Statement := by
  classical
  intro n d W I φ f hW hdim hφ hI hf hfc δ hδ
  by_cases hA : ∃ A : Matrix (Fin d) (Fin n) ℂ, IsFiniteProjection W A
  swap
  · refine ⟨Set.univ, isOpen_univ, Set.subset_univ _, fun χ _ _ _ => ?_⟩
    unfold varInt
    rw [dif_neg hA, abs_zero]
    exact hδ.le
  set A := hA.choose with hAdef
  have hAf : IsFiniteProjection W A := hA.choose_spec
  have hvar : ∀ g, varInt W d g φ = ∫ y, chartDens W A g φ y := fun g => by
    unfold varInt chartInt
    rw [dif_pos hA]
  have hfin : ∀ y, (fibre W A y).Finite := fun y => (FibreBound.proof n d W A hW hdim hAf y).2.1
  have hS : IsClosed (zeroSet I) := SheetSumMeasurable.isClosed_zeroSet I
  set U : ℕ → Set (Fin n → ℂ) := fun k => Metric.thickening (1 / ((k : ℝ) + 1)) (zeroSet I) with hU
  set F : ℕ → (Fin d → ℂ) → ℝ := fun k => chartAbsDens W A ((U k).indicator fun x => |f x|) φ with hF
  set G := chartAbsDens W A (fun x => |f x|) φ with hG
  have hGi : Integrable G := hCMC n d W A _ φ hW hdim hAf (continuous_abs.comp hf).continuousOn hφ
    (Or.inl (hfc.comp_left abs_zero))
  have hFm : ∀ k, Measurable (F k) := fun k => (SheetSumMeasurable.proof n d W A _ φ hW hdim hAf
    ((continuous_abs.comp hf).measurable.indicator Metric.isOpen_thickening.measurableSet) hφ).2
  have hFG : ∀ k y, ‖F k y‖ ≤ G y := by
    intro k y
    rw [Real.norm_eq_abs]
    refine abs_sheetSum_le W A (fun x s => ?_) (hfin y)
    rw [abs_abs, abs_mul, abs_mul]
    refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
    by_cases hx : x ∈ U k
    · simp [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx, abs_zero]
      exact abs_nonneg _
  have hlim : ∀ᵐ y, Tendsto (fun k => F k y) atTop (𝓝 0) := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 (volume_image_eq_zero W I A hI)] with y hy
    have hx : ∀ x ∈ fibre W A y, ∀ᶠ k in atTop, x ∉ U k := by
      intro x hxf
      have hxS : x ∉ zeroSet I := fun h => hy ⟨x, ⟨hxf.1, h⟩, hxf.2⟩
      obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hS.isOpen_compl x hxS
      obtain ⟨K, hK⟩ := exists_nat_one_div_lt hε
      filter_upwards [eventually_ge_atTop K] with k hk hxU
      obtain ⟨z, hz, hdist⟩ := Metric.mem_thickening_iff.1 hxU
      have hKk : (K : ℝ) + 1 ≤ (k : ℝ) + 1 := by
        have : (K : ℝ) ≤ k := by exact_mod_cast hk
        linarith
      have hle : 1 / ((k : ℝ) + 1) ≤ 1 / ((K : ℝ) + 1) :=
        one_div_le_one_div_of_le (by positivity) hKk
      exact hball (show dist z x < ε by rw [dist_comm]; linarith) hz
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [(eventually_all_finite (hfin y)).2 hx] with k hk
    symm
    show sheetSum W A _ y = 0
    unfold sheetSum
    rw [finsum_mem_eq_finite_toFinset_sum _ (hfin y)]
    refine Finset.sum_eq_zero fun x hxm => ?_
    rw [Set.Finite.mem_toFinset] at hxm
    split_ifs <;> simp [Set.indicator_of_notMem (hk x hxm)]
  have hT := tendsto_integral_of_dominated_convergence G (fun k => (hFm k).aestronglyMeasurable) hGi
    (fun k => Eventually.of_forall (hFG k)) hlim
  simp only [integral_zero] at hT
  obtain ⟨k, hk⟩ := ((tendsto_order.1 hT).2 δ hδ).exists
  refine ⟨U k, Metric.isOpen_thickening, Metric.self_subset_thickening (by positivity) _,
    fun χ hχ hχ1 hχU => ?_⟩
  have hFi : Integrable (F k) := hGi.mono' (hFm k).aestronglyMeasurable (Eventually.of_forall (hFG k))
  have hpt : ∀ y, ‖chartDens W A (fun x => χ x * f x) φ y‖ ≤ F k y := by
    intro y
    rw [Real.norm_eq_abs]
    refine abs_sheetSum_le W A (fun x s => ?_) (hfin y)
    by_cases hx : x ∈ U k
    · rw [Set.indicator_of_mem hx, abs_mul, abs_mul, abs_mul, abs_abs]
      exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_left (abs_nonneg _) (hχ1 x)) (abs_nonneg _)
    · have h0 : χ x = 0 := image_eq_zero_of_notMem_tsupport fun h => hx (hχU h)
      simp only [h0, zero_mul, abs_zero]
      positivity
  have h1 := norm_integral_le_of_norm_le hFi (Eventually.of_forall hpt)
  rw [Real.norm_eq_abs, ← hvar] at h1
  exact h1.trans hk.le

end

end GroundTheory.Heights₂.Heights
