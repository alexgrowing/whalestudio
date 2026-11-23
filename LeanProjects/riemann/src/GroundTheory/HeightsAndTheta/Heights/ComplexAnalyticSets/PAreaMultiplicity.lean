import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StAreaMultiplicity
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Module Set Filter Function

open scoped ENNReal NNReal

noncomputable section

theorem areaJacobian_eq_abs_det_comp {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (φ : F ≃ₗᵢ[ℝ] E) (L : E →ₗ[ℝ] F) :
    areaJacobian L = |LinearMap.det (φ.toLinearIsometry.toLinearMap ∘ₗ L)| := by
  have h1 : areaJacobian L = L.normDet := by
    have h := L.normDet_sq
    simp only [RCLike.ofReal_real_eq_id, id_eq] at h
    rw [areaJacobian, ← h, Real.sqrt_sq L.normDet_nonneg]
  rw [h1, ← LinearMap.normDet_eq_abs_det,
    LinearMap.normDet_comp_of_finrank_eq _ _ φ.toLinearEquiv.finrank_eq.symm,
    φ.toLinearIsometry.normDet_eq_one, one_mul]

theorem encard_iUnion_nat_eq_tsum {α : Type*} (s : ℕ → Set α) (hs : Pairwise (Disjoint on s)) :
    (((⋃ n, s n).encard : ℕ∞) : ℝ≥0∞) = ∑' n, (((s n).encard : ℕ∞) : ℝ≥0∞) := by
  let _ : MeasurableSpace α := ⊤
  have hm : ∀ t : Set α, MeasurableSet t := fun _ => MeasurableSpace.measurableSet_top
  rw [← Measure.count_apply (hm _), measure_iUnion hs (fun _ => hm _)]
  simp only [Measure.count_apply (hm _)]

theorem lintegral_abs_det_eq_lintegral_encard {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure] {A : Set E} {f : E → E} {f' : E → E →L[ℝ] E}
    (hA : MeasurableSet A) (hf' : ∀ x ∈ A, HasFDerivWithinAt f (f' x) A x) :
    ∫⁻ x in A, ENNReal.ofReal |(f' x).det| ∂μ =
      ∫⁻ y, (({x ∈ A | f x = y}.encard : ℕ∞) : ℝ≥0∞) ∂μ := by
  classical
  set B : Set E := {x ∈ A | (f' x).det ≠ 0} with hBdef
  have hBA : B ⊆ A := sep_subset _ _

  have hB : NullMeasurableSet B μ := by
    obtain ⟨d, hdm, hfd⟩ : AEMeasurable (fun x => (f' x).det) (μ.restrict A) :=
      ContinuousLinearMap.continuous_det.measurable.comp_aemeasurable
        (aemeasurable_fderivWithin μ hA hf')
    refine (hA.inter (hdm (measurableSet_singleton 0).compl)).nullMeasurableSet.congr ?_
    filter_upwards [(ae_restrict_iff' hA).1 hfd] with x hx
    change (x ∈ A ∩ d ⁻¹' {0}ᶜ) = (x ∈ B)
    rw [eq_iff_iff]
    by_cases hxA : x ∈ A
    · simp [B, hxA, hx hxA]
    · simp [B, hxA]

  have hZ : μ (f '' {x ∈ A | (f' x).det = 0}) = 0 :=
    addHaar_image_eq_zero_of_det_fderivWithin_eq_zero μ
      (fun x hx => (hf' x hx.1).mono (sep_subset _ _)) (fun x hx => hx.2)

  let r : (E →L[ℝ] E) → ℝ≥0 := fun L => (‖L.inverse‖₊ + 1)⁻¹
  obtain ⟨t, L, htd, htm, hcov, happ, hL⟩ :=
    exists_partition_approximatesLinearOn_of_hasFDerivWithinAt f B f'
      (fun x hx => (hf' x hx.1).mono hBA) r (fun _ => inv_ne_zero (by positivity))
  set P : ℕ → Set E := fun n => B ∩ t n with hPdef
  have hPm : ∀ n, NullMeasurableSet (P n) μ := fun n => hB.inter (htm n).nullMeasurableSet
  have hPd : Pairwise (Disjoint on P) := fun m n hmn =>
    (htd hmn).mono inter_subset_right inter_subset_right
  have hPA : ∀ n, P n ⊆ A := fun n => inter_subset_left.trans hBA
  have hderP : ∀ n, ∀ x ∈ P n, HasFDerivWithinAt f (f' x) (P n) x := fun n x hx =>
    (hf' x (hPA n hx)).mono (hPA n)
  have hinj : ∀ n, InjOn f (P n) := by
    intro n
    rcases (P n).eq_empty_or_nonempty with h | ⟨x, hx⟩
    · rw [h]; exact injOn_empty f
    obtain ⟨y, hy, hLy⟩ := hL ⟨x, hx.1⟩ n
    set e := (f' y).toContinuousLinearEquivOfDetNeZero hy.2
    have he : (e : E →L[ℝ] E) = L n := by
      rw [hLy]; exact ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero _ _
    have ha := happ n
    rw [← he] at ha
    refine ha.injOn ?_
    rcases subsingleton_or_nontrivial E with hE | hE
    · exact Or.inl hE
    right
    have hr : r (e : E →L[ℝ] E) = (‖(e.symm : E →L[ℝ] E)‖₊ + 1)⁻¹ := by
      simp only [r, ContinuousLinearMap.inverse_equiv]
    rw [hr]
    have hpos : 0 < ‖(e.symm : E →L[ℝ] E)‖₊ := by
      rw [pos_iff_ne_zero, ne_eq, nnnorm_eq_zero]
      intro h0
      obtain ⟨z, hz⟩ := exists_ne (0 : E)
      apply hz
      simpa using congrArg (fun T : E →L[ℝ] E => T (e z)) h0
    exact (inv_lt_inv₀ (by positivity) hpos).2 (lt_add_one _)
  have hBU : B = ⋃ n, P n := by
    rw [← inter_iUnion]; exact (inter_eq_left.2 hcov).symm
  have himg : ∀ n, NullMeasurableSet (f '' P n) μ := fun n =>
    nullMeasurable_image_of_fderivWithin μ (hPm n) (hderP n) (hinj n)
  calc ∫⁻ x in A, ENNReal.ofReal |(f' x).det| ∂μ
      = ∫⁻ x in B, ENNReal.ofReal |(f' x).det| ∂μ := by
        rw [← lintegral_indicator hA, ← lintegral_indicator₀ hB]
        congr 1; ext x
        by_cases hx : x ∈ A
        · by_cases hd : (f' x).det = 0
          · simp [indicator, hx, hd, B]
          · simp [indicator, hx, hd, B]
        · have : x ∉ B := fun h => hx h.1
          simp [hx, this]
    _ = ∑' n, ∫⁻ x in P n, ENNReal.ofReal |(f' x).det| ∂μ := by
        rw [hBU]; exact lintegral_iUnion₀ hPm (fun m n hmn => (hPd hmn).aedisjoint) _
    _ = ∑' n, μ (f '' P n) := tsum_congr fun n =>
        lintegral_abs_det_fderiv_eq_addHaar_image₀ μ (hPm n) (hderP n) (hinj n)
    _ = ∑' n, ∫⁻ y, (f '' P n).indicator 1 y ∂μ :=
        tsum_congr fun n => (lintegral_indicator_one₀ (himg n)).symm
    _ = ∫⁻ y, ∑' n, (f '' P n).indicator 1 y ∂μ :=
        (lintegral_tsum fun n => aemeasurable_one.indicator₀ (himg n)).symm
    _ = ∫⁻ y, (({x ∈ A | f x = y}.encard : ℕ∞) : ℝ≥0∞) ∂μ := by
        apply lintegral_congr_ae
        filter_upwards [measure_eq_zero_iff_ae_notMem.1 hZ] with y hy
        have hU : {x ∈ A | f x = y} = ⋃ n, {x ∈ P n | f x = y} := by
          ext x
          simp only [mem_ofPred_eq, mem_iUnion]
          constructor
          · rintro ⟨hxA, hxy⟩
            have hxB : x ∈ B := ⟨hxA, fun hd => hy ⟨x, ⟨hxA, hd⟩, hxy⟩⟩
            obtain ⟨n, hn⟩ := mem_iUnion.1 (hcov hxB)
            exact ⟨n, ⟨hxB, hn⟩, hxy⟩
          · rintro ⟨n, hxP, hxy⟩
            exact ⟨hPA n hxP, hxy⟩
        rw [hU, encard_iUnion_nat_eq_tsum _ (fun m n hmn => (hPd hmn).mono (sep_subset _ _)
          (sep_subset _ _))]
        refine tsum_congr fun n => ?_
        by_cases hyn : y ∈ f '' P n
        · obtain ⟨x, hx, rfl⟩ := hyn
          have hs : {z ∈ P n | f z = f x} = {x} := by
            ext z
            simp only [mem_ofPred_eq, mem_singleton_iff]
            exact ⟨fun h => hinj n h.1 hx h.2, fun h => by subst h; exact ⟨hx, rfl⟩⟩
          rw [hs, encard_singleton, indicator_of_mem (mem_image_of_mem f hx)]
          simp
        · have hs : {z ∈ P n | f z = y} = ∅ := by
            ext z
            simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
            exact fun hz e => hyn ⟨z, hz, e⟩
          rw [hs, encard_empty]
          simp [hyn]

theorem AreaMultiplicity.proof : AreaMultiplicity.Statement := by
  intro E F _ _ _ _ _ _ _ _ _ _ k hE hF A f f' hA hf'
  subst hE
  let φ : F ≃ₗᵢ[ℝ] E := (stdOrthonormalBasis ℝ F).equiv (stdOrthonormalBasis ℝ E) (finCongr hF)
  let g : E → E := fun x => φ (f x)
  let g' : E → E →L[ℝ] E := fun x => (φ.toContinuousLinearEquiv : F →L[ℝ] E).comp (f' x)
  have hg' : ∀ x ∈ A, HasFDerivWithinAt g (g' x) A x := fun x hx =>
    (φ.toContinuousLinearEquiv : F →L[ℝ] E).hasFDerivAt.comp_hasFDerivWithinAt x (hf' x hx)
  have hJ : ∀ x, ENNReal.ofReal (areaJacobian (f' x : E →ₗ[ℝ] F)) =
      ENNReal.ofReal |(g' x).det| := by
    intro x
    rw [areaJacobian_eq_abs_det_comp φ]
    rfl
  have hN : ∀ y, {x ∈ A | f x = y} = {x ∈ A | g x = φ y} := by
    intro y; ext x; simp [g]
  simp_rw [hJ, hN]
  rw [lintegral_abs_det_eq_lintegral_encard μH[(finrank ℝ E : ℝ)] hA hg']
  have hφ : MeasurePreserving φ (μH[(finrank ℝ E : ℝ)] : Measure F) μH[(finrank ℝ E : ℝ)] :=
    φ.toIsometryEquiv.measurePreserving_hausdorffMeasure _
  have hφe : MeasurableEmbedding φ := φ.toHomeomorph.measurableEmbedding
  exact (hφ.lintegral_comp_emb hφe (fun z => (({x ∈ A | g x = z}.encard : ℕ∞) : ℝ≥0∞))).symm

end

end GroundTheory.Heights₂.Heights
