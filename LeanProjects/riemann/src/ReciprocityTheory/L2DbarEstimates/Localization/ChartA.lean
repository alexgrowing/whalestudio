import ReciprocityTheory.L2DbarEstimates.Localization.UnweightBackStatement
import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.Imports

namespace ReciprocityTheory.L2DbarEstimates.F

open MeasureTheory Filter Topology Set Function
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff

noncomputable section

section Tr

variable {M : Type*} [TopologicalSpace M] [SecondCountableTopology M] [MeasurableSpace M]
  [BorelSpace M] {n : ℕ} {z : M → V n} {e : OpenPartialHomeomorph M (V n)}

theorem chT_aem_symm : AEMeasurable (e.symm : V n → M) (volume.restrict e.target) := e.continuousOn_symm.aemeasurable e.open_target.measurableSet

theorem chT_lint (hz : IsLocalHomeomorph z) (he : IsChart n z e) (f : M → ℝ≥0∞)
    (hf : AEMeasurable f (vol n z)) (hs : ∀ x, x ∉ e.source → f x = 0) :
    ∫⁻ x, f x ∂vol n z = ∫⁻ y in e.target, f (e.symm y) := by
  have hsub : Function.support f ⊆ e.source := fun x hx => by
    by_contra h; exact hx (hs x h)
  rw [← setLIntegral_eq_of_support_subset hsub, vol_restrict_source n z hz e he]
  have hf' : AEMeasurable f (Measure.map e.symm (volume.restrict e.target)) := by
    rw [← vol_restrict_source n z hz e he]; exact hf.restrict
  exact lintegral_map' hf' (chT_aem_symm (e := e))

theorem chT_int {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (hz : IsLocalHomeomorph z)
    (he : IsChart n z e) (f : M → E)
    (hf : AEStronglyMeasurable f (vol n z)) (hs : ∀ x, x ∉ e.source → f x = 0) :
    ∫ x, f x ∂vol n z = ∫ y in e.target, f (e.symm y) := by
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hs, vol_restrict_source n z hz e he]
  have hf' : AEStronglyMeasurable f (Measure.map e.symm (volume.restrict e.target)) := by
    rw [← vol_restrict_source n z hz e he]; exact hf.restrict
  exact integral_map (chT_aem_symm (e := e)) hf'

theorem chT_aesm {E : Type*} [NormedAddCommGroup E] (hz : IsLocalHomeomorph z)
    (he : IsChart n z e) (f : M → E) (hf : AEStronglyMeasurable f (vol n z)) :
    AEStronglyMeasurable (e.target.indicator (f ∘ e.symm)) volume := by
  have hf' : AEStronglyMeasurable f (Measure.map e.symm (volume.restrict e.target)) := by
    rw [← vol_restrict_source n z hz e he]; exact hf.restrict
  exact (aestronglyMeasurable_indicator_iff e.open_target.measurableSet).2
    (hf'.comp_aemeasurable (chT_aem_symm (e := e)))

theorem chartTransport_indicator_memLp_two {E : Type*} [NormedAddCommGroup E] [T2Space M] (hz : IsLocalHomeomorph z)
    (he : IsChart n z e) (f : M → E) (hf : LocalL2Isometry (vol n z) f) (hc : HasCompactSupport f)
    (hsub : tsupport f ⊆ e.source) :
    MemLp (e.target.indicator (f ∘ e.symm)) 2 volume := by
  have hae := chT_aesm hz he f hf.1
  refine ⟨hae, ?_⟩
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top two_ne_zero ENNReal.ofNat_ne_top]
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two]
  have hz0 : ∀ x, x ∉ tsupport f → f x = 0 := fun x hx => image_eq_zero_of_notMem_tsupport hx
  have hs : ∀ x, x ∉ e.source → ‖f x‖ₑ ^ 2 = 0 := by
    intro x hx
    simp [hz0 x (fun h => hx (hsub h))]
  have e1 : ∫⁻ y, ‖e.target.indicator (f ∘ e.symm) y‖ₑ ^ 2 =
      ∫⁻ y in e.target, ‖f (e.symm y)‖ₑ ^ 2 := by
    rw [← lintegral_indicator e.open_target.measurableSet]
    congr 1; funext y
    by_cases hy : y ∈ e.target <;> simp [hy]
  rw [e1, ← chT_lint hz he (fun x => ‖f x‖ₑ ^ 2) (hf.1.enorm.pow_const 2) hs]
  calc ∫⁻ x, ‖f x‖ₑ ^ 2 ∂vol n z = ∫⁻ x in tsupport f, ‖f x‖ₑ ^ 2 ∂vol n z := by
        rw [setLIntegral_eq_of_support_subset]
        intro x hx
        by_contra h
        exact hx (by simp [hz0 x h])
    _ < ⊤ := hf.2 _ hc

end Tr

theorem chT_plateau {n : ℕ} (K U : Set (V n)) (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ ρ : V n → ℝ, ContDiff ℝ ∞ ρ ∧ HasCompactSupport ρ ∧ tsupport ρ ⊆ U ∧
      ∃ O : Set (V n), IsOpen O ∧ K ⊆ O ∧ ∀ y ∈ O, ρ y = 1 := by
  obtain ⟨δ, hδ, hδU⟩ := hK.exists_cthickening_subset_open hU hKU
  obtain ⟨t, htK, htf, hcov⟩ := hK.finite_cover_balls (e := δ / 3) (by positivity)
  let bx : ∀ x : V n, ContDiffBump x := fun x => ⟨δ / 3, 2 * δ / 3, by positivity, by linarith⟩
  let ψ : V n → ℝ := fun y => ∑ x ∈ htf.toFinset, bx x y
  let ρ : V n → ℝ := fun y => Real.smoothTransition (ψ y)
  have hψd : ContDiff ℝ ∞ ψ := ContDiff.sum fun x _ => (bx x).contDiff
  have hρd : ContDiff ℝ ∞ ρ := Real.smoothTransition.contDiff.comp hψd
  have hsuppψ : ∀ y, ψ y ≠ 0 → y ∈ Metric.cthickening (2 * δ / 3) K := by
    intro y hy
    obtain ⟨x, hx, hxy⟩ := Finset.exists_ne_zero_of_sum_ne_zero hy
    have hb : y ∈ Metric.ball x (bx x).rOut := by rw [← (bx x).support_eq]; exact hxy
    exact Metric.thickening_subset_cthickening _ _
      (Metric.ball_subset_thickening (htK (htf.mem_toFinset.1 hx)) _ hb)
  have hsuppρ : ∀ y, y ∉ Metric.cthickening (2 * δ / 3) K → ρ y = 0 := by
    intro y hy
    have : ψ y = 0 := by by_contra h; exact hy (hsuppψ y h)
    simp only [ρ, this, Real.smoothTransition.zero]
  have hts : tsupport ρ ⊆ Metric.cthickening (2 * δ / 3) K :=
    closure_minimal (fun y hy => by by_contra h; exact hy (hsuppρ y h)) Metric.isClosed_cthickening
  refine ⟨ρ, hρd, HasCompactSupport.intro hK.cthickening hsuppρ,
    hts.trans ((Metric.cthickening_mono (by linarith) K).trans hδU),
    ⋃ x ∈ t, Metric.ball x (δ / 3), isOpen_biUnion fun _ _ => Metric.isOpen_ball, hcov, ?_⟩
  intro y hy
  simp only [Set.mem_iUnion] at hy
  obtain ⟨x, hx, hxy⟩ := hy
  have h1 : bx x y = 1 := (bx x).one_of_mem_closedBall (Metric.ball_subset_closedBall hxy)
  have h2 : 1 ≤ ψ y := by
    calc (1 : ℝ) = bx x y := h1.symm
      _ ≤ ψ y := Finset.single_le_sum (f := fun x' => bx x' y) (fun x' _ => (bx x').nonneg)
          (htf.mem_toFinset.2 hx)
  exact Real.smoothTransition.one_of_one_le h2

theorem chT_comp {n : ℕ} {M : Type*} [MeasurableSpace M] (μ : Measure M) (G : M → V n)
    (hG : AEStronglyMeasurable G μ) (j : Fin n) : AEStronglyMeasurable (fun x => G x j) μ := (EuclideanSpace.proj (𝕜 := ℂ) j).continuous.comp_aestronglyMeasurable hG

section Main

variable {M : Type*} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [MeasurableSpace M] [BorelSpace M] {n : ℕ} {z : M → V n} {e : OpenPartialHomeomorph M (V n)}

theorem chT_test (hExt : ExtendStatement n M) (hz : IsLocalHomeomorph z) (he : IsChart n z e)
    (ψ : V n → ℂ) (hψd : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (hψt : tsupport ψ ⊆ e.target) :
    IsTest n z (e.source.indicator (ψ ∘ e)) ∧
    (∀ y ∈ e.target, e.source.indicator (ψ ∘ e) (e.symm y) = ψ y) ∧
    (∀ j, ∀ y ∈ e.target, d n z j (e.source.indicator (ψ ∘ e)) (e.symm y) = wd n j ψ y ∧
        db n z j (e.source.indicator (ψ ∘ e)) (e.symm y) = wdb n j ψ y) := by
  obtain ⟨h1, h2, -, h4⟩ := hExt z hz e ψ he hψd hψc hψt
  refine ⟨⟨h1, h2⟩, fun y hy => ?_, fun j y hy => ?_⟩
  · rw [Set.indicator_of_mem (e.map_target hy), Function.comp_apply, e.right_inv hy]
  · have := h4 j (e.symm y) (e.map_target hy)
    rw [e.right_inv hy] at this
    exact this

theorem chT_mulρ (ρ : V n → ℝ) (hρd : ContDiff ℝ ∞ ρ) (hρc : HasCompactSupport ρ)
    (U : Set (V n)) (hρt : tsupport ρ ⊆ U) (φ : V n → ℂ) (hφd : ContDiff ℝ ∞ φ) :
    ContDiff ℝ ∞ (fun y => (ρ y : ℂ) * φ y) ∧ HasCompactSupport (fun y => (ρ y : ℂ) * φ y) ∧
      tsupport (fun y => (ρ y : ℂ) * φ y) ⊆ U := by
  refine ⟨(Complex.ofRealCLM.contDiff.comp hρd).mul hφd, ?_, ?_⟩
  · exact (hρc.comp_left Complex.ofReal_zero).mul_right
  · exact tsupport_mul_subset_left.trans ((tsupport_comp_subset Complex.ofReal_zero ρ).trans hρt)

theorem chT_wd (ρ : V n → ℝ) (φ : V n → ℂ) (O : Set (V n)) (hOo : IsOpen O)
    (h1 : ∀ y ∈ O, ρ y = 1) (y : V n) (hy : y ∈ O) (j : Fin n) :
    wd n j (fun y => (ρ y : ℂ) * φ y) y = wd n j φ y ∧
      wdb n j (fun y => (ρ y : ℂ) * φ y) y = wdb n j φ y := by
  have hev : (fun y => (ρ y : ℂ) * φ y) =ᶠ[𝓝 y] φ := by
    filter_upwards [hOo.mem_nhds hy] with w hw
    rw [h1 w hw]; simp
  have := hev.fderiv_eq (𝕜 := ℝ)
  unfold wd wdb
  rw [this]
  exact ⟨rfl, rfl⟩

end Main

end

end ReciprocityTheory.L2DbarEstimates.F
