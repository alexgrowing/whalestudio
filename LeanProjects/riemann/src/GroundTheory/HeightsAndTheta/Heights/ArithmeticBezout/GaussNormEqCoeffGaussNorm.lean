import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Statements
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.SpecFirstDetFormNeZero
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory NumberField Matrix ProbabilityTheory

noncomputable section

namespace ObjectsHeight

variable {n : ℕ}

theorem euclid_norm_eq (v : Fin n → ℂ) : ‖WithLp.toLp 2 v‖ = √(∑ i, ‖v i‖ ^ 2) := by
  rw [EuclideanSpace.norm_eq]

theorem isUnit_det_of_isUnit {S : Matrix (Fin n) (Fin n) ℂ} (hS : IsUnit S) : IsUnit S.det :=
  (Matrix.isUnit_iff_isUnit_det S).mp hS

def ofPointMatrix (S : Matrix (Fin n) (Fin n) ℂ) (hS : IsUnit S) : HermNorm n where
  mat := (S⁻¹)ᵀ
  isUnit_det := by
    rw [det_transpose, det_nonsing_inv]
    exact (isUnit_det_of_isUnit hS).ringInverse

theorem ofPointMatrix_norm (S : Matrix (Fin n) (Fin n) ℂ) (hS : IsUnit S) (u : Fin n → ℂ) :
    (ofPointMatrix S hS).norm u = IndefiniteRowSideFullHecke.ArithBezout.formNorm S u := by
  rw [IndefiniteRowSideFullHecke.ArithBezout.formNorm, euclid_norm_eq]
  rfl

theorem ofPointMatrix_dualNorm (S : Matrix (Fin n) (Fin n) ℂ) (hS : IsUnit S) (y : Fin n → ℂ) :
    (ofPointMatrix S hS).dualNorm y = (IndefiniteRowSideFullHecke.ArithBezout.pointMetric S hS).ρ y := by
  have h : ((ofPointMatrix S hS).matᵀ)⁻¹ = S := by
    simp only [ofPointMatrix, transpose_transpose]
    exact nonsing_inv_nonsing_inv S (isUnit_det_of_isUnit hS)
  simp only [HermNorm.dualNorm, h, IndefiniteRowSideFullHecke.ArithBezout.pointMetric, euclid_norm_eq]

theorem ofPointMatrix_fsLog (S : Matrix (Fin n) (Fin n) ℂ) (hS : IsUnit S) (u y : Fin n → ℂ) :
    fsLog (ofPointMatrix S hS) u y =
      IndefiniteRowSideFullHecke.ArithBezout.logFormNorm S hS u (fun p => y p.2) := by
  simp [fsLog, IndefiniteRowSideFullHecke.ArithBezout.logFormNorm, IndefiniteRowSideFullHecke.ArithBezout.hermLine,
    ReciprocityTheory.ChartRestriction.G.Geo.HermLine.ofMetrics, ofPointMatrix_dualNorm]

theorem exists_eq_ofPointMatrix (h : HermNorm n) :
    ∃ (S : Matrix (Fin n) (Fin n) ℂ) (hS : IsUnit S), h = ofPointMatrix S hS := by
  have hA : IsUnit h.mat := (Matrix.isUnit_iff_isUnit_det _).mpr h.isUnit_det
  refine ⟨(h.matᵀ)⁻¹, (Matrix.isUnit_nonsing_inv_iff).mpr ((isUnit_transpose _).mpr hA), ?_⟩
  cases h with
  | mk A hAdet =>
    simp only [ofPointMatrix, HermNorm.mk.injEq]
    rw [nonsing_inv_nonsing_inv _ (by rw [det_transpose]; exact hAdet), transpose_transpose]

theorem std_eq_ofPointMatrix_one : HermNorm.std n = ofPointMatrix 1 isUnit_one := by
  simp [HermNorm.std, ofPointMatrix]

theorem formNorm_transpose_mulVec {S : Matrix (Fin n) (Fin n) ℂ} (hS : IsUnit S) (v : Fin n → ℂ) :
    IndefiniteRowSideFullHecke.ArithBezout.formNorm S (Sᵀ *ᵥ v) = √(IndefiniteRowSideFullHecke.ArithBezout.normSq v) := by
  rw [IndefiniteRowSideFullHecke.ArithBezout.formNorm, mulVec_mulVec, ← transpose_mul,
    mul_nonsing_inv S (isUnit_det_of_isUnit hS), transpose_one, one_mulVec, euclid_norm_eq]
  rfl

theorem cond_map_equiv {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] (e : α ≃ᵐ β)
    (μ : Measure α) (s : Set β) : (cond μ (e ⁻¹' s)).map e = cond (μ.map e) s := by
  rw [ProbabilityTheory.cond, ProbabilityTheory.cond, Measure.map_smul, ← e.restrict_map,
    e.map_apply]

theorem cond_smul {α : Type*} [MeasurableSpace α] (μ : Measure α) (s : Set α)
    {c : ENNReal} (h0 : c ≠ 0) (htop : c ≠ ⊤) : cond (c • μ) s = cond μ s := by
  rw [ProbabilityTheory.cond, ProbabilityTheory.cond, Measure.restrict_smul, Measure.smul_apply, smul_smul, smul_eq_mul,
    ENNReal.mul_inv (Or.inl h0) (Or.inl htop), mul_comm c⁻¹, mul_assoc,
    ENNReal.inv_mul_cancel h0 htop, mul_one]

theorem cond_congr_set {α : Type*} [MeasurableSpace α] (μ : Measure α) {s t : Set α}
    (h : s =ᵐ[μ] t) : cond μ s = cond μ t := by
  rw [ProbabilityTheory.cond, ProbabilityTheory.cond, measure_congr h, Measure.restrict_congr_set h]

variable {k : ℕ}

theorem map_curry_volume :
    (volume : Measure (Fin k × Fin n → ℂ)).map (MeasurableEquiv.curry (Fin k) (Fin n) ℂ) =
      Measure.pi fun _ : Fin k => (volume : Measure (Fin n → ℂ)) := by
  rw [MeasurableEquiv.map_apply_eq_iff_map_symm_apply_eq]
  show Measure.pi (fun _ : Fin k × Fin n => (volume : Measure ℂ)) = _
  refine Measure.pi_eq fun s hs => ?_
  rw [MeasurableEquiv.map_apply, MeasurableEquiv.coe_curry_symm]
  have hset : Function.uncurry ⁻¹' Set.univ.pi s =
      Set.univ.pi fun i : Fin k => Set.univ.pi fun j : Fin n => s (i, j) := by
    ext x
    simp
  rw [hset, Measure.pi_pi]
  simp_rw [volume_pi, Measure.pi_pi]
  rw [Fintype.prod_prod_type]

theorem volume_normSq_eq_one :
    (volume : Measure (Fin n → ℂ)) {v | IndefiniteRowSideFullHecke.ArithBezout.normSq v = 1} = 0 := by
  rcases n with _ | m
  · have : {v : Fin 0 → ℂ | IndefiniteRowSideFullHecke.ArithBezout.normSq v = 1} = ∅ := by
      ext v
      simp [IndefiniteRowSideFullHecke.ArithBezout.normSq]
    rw [this, measure_empty]
  · let e : (Fin (m + 1) → ℂ) ≃L[ℝ] EuclideanSpace ℂ (Fin (m + 1)) :=
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (m + 1) => ℂ)).symm
    have : (volume.map e).IsAddHaarMeasure := e.isAddHaarMeasure_map _
    have hset : {v : Fin (m + 1) → ℂ | IndefiniteRowSideFullHecke.ArithBezout.normSq v = 1} =
        e ⁻¹' Metric.sphere 0 1 := by
      ext v
      simp only [Set.mem_ofPred_eq, Set.mem_preimage, mem_sphere_zero_iff_norm]
      have : ‖e v‖ = √(IndefiniteRowSideFullHecke.ArithBezout.normSq v) := by
        show ‖WithLp.toLp 2 v‖ = _
        rw [euclid_norm_eq]
        rfl
      rw [this, Real.sqrt_eq_one]
    rw [hset, ← Measure.map_apply e.continuous.measurable Metric.isClosed_sphere.measurableSet]
    exact Measure.addHaar_sphere _ 0 1

def blockMul (A : Matrix (Fin n) (Fin n) ℂ) (u : Fin k × Fin n → ℂ) : Fin k × Fin n → ℂ :=
  fun p => (A *ᵥ fun j => u (p.1, j)) p.2

theorem blockMul_mul (A B : Matrix (Fin n) (Fin n) ℂ) (u : Fin k × Fin n → ℂ) :
    blockMul A (blockMul B u) = blockMul (A * B) u := by
  funext p
  show (A *ᵥ (B *ᵥ fun j => u (p.1, j))) p.2 = ((A * B) *ᵥ fun j => u (p.1, j)) p.2
  rw [mulVec_mulVec]

theorem blockMul_one (u : Fin k × Fin n → ℂ) : blockMul 1 u = u := by
  funext p
  show ((1 : Matrix (Fin n) (Fin n) ℂ) *ᵥ fun j => u (p.1, j)) p.2 = u p
  rw [one_mulVec]

def blockEquiv (S : Matrix (Fin n) (Fin n) ℂ) (hS : IsUnit S) :
    (Fin k × Fin n → ℂ) ≃ₗ[ℝ] (Fin k × Fin n → ℂ) where
  toFun := blockMul Sᵀ
  invFun := blockMul (S⁻¹)ᵀ
  map_add' u v := by
    funext p
    show (Sᵀ *ᵥ fun j => (u + v) (p.1, j)) p.2 =
      (Sᵀ *ᵥ fun j => u (p.1, j)) p.2 + (Sᵀ *ᵥ fun j => v (p.1, j)) p.2
    rw [show (fun j => (u + v) (p.1, j)) = (fun j => u (p.1, j)) + fun j => v (p.1, j)
      from rfl, mulVec_add]
    rfl
  map_smul' c u := by
    funext p
    show (Sᵀ *ᵥ fun j => (c • u) (p.1, j)) p.2 = c • (Sᵀ *ᵥ fun j => u (p.1, j)) p.2
    rw [show (fun j => (c • u) (p.1, j)) = c • fun j => u (p.1, j) from rfl, mulVec_smul]
    rfl
  left_inv u := by
    show blockMul (S⁻¹)ᵀ (blockMul Sᵀ u) = u
    rw [blockMul_mul, ← transpose_mul, mul_nonsing_inv S (isUnit_det_of_isUnit hS),
      transpose_one, blockMul_one]
  right_inv u := by
    show blockMul Sᵀ (blockMul (S⁻¹)ᵀ u) = u
    rw [blockMul_mul, ← transpose_mul, nonsing_inv_mul S (isUnit_det_of_isUnit hS),
      transpose_one, blockMul_one]

theorem continuous_formNorm (S : Matrix (Fin n) (Fin n) ℂ) :
    Continuous (IndefiniteRowSideFullHecke.ArithBezout.formNorm S) := by
  unfold IndefiniteRowSideFullHecke.ArithBezout.formNorm
  exact continuous_norm.comp ((PiLp.continuous_toLp 2 _).comp
    (Continuous.matrix_mulVec continuous_const continuous_id))

theorem continuous_normSq : Continuous (IndefiniteRowSideFullHecke.ArithBezout.normSq (n := n)) := by
  unfold IndefiniteRowSideFullHecke.ArithBezout.normSq
  fun_prop

theorem sphereMean_eq_integral (S : Matrix (Fin n) (Fin n) ℂ) (hS : IsUnit S) (h : HermNorm n)
    (hh : ∀ u, h.norm u = IndefiniteRowSideFullHecke.ArithBezout.formNorm S u) (g : (Fin k × Fin n → ℂ) → ℝ)
    (hg : Measurable g) :
    sphereMean h k g = ∫ u, g u ∂IndefiniteRowSideFullHecke.ArithBezout.formSphereLaw S k := by
  have hN : h.norm = IndefiniteRowSideFullHecke.ArithBezout.formNorm S := funext hh

  let E := blockEquiv (k := k) S hS
  let F : (Fin k × Fin n → ℂ) ≃ᵐ (Fin k × Fin n → ℂ) :=
    E.toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv
  have hF : ⇑F = blockMul Sᵀ := rfl
  let Nf : (Fin k × Fin n → ℂ) → (Fin k × Fin n → ℂ) := fun u ij =>
    ((IndefiniteRowSideFullHecke.ArithBezout.formNorm S fun j => u (ij.1, j) : ℝ) : ℂ)⁻¹ * u ij
  let R : (Fin n → ℂ) → (Fin n → ℂ) := fun u => (Real.sqrt (IndefiniteRowSideFullHecke.ArithBezout.normSq u))⁻¹ • u
  let T : (Fin k → Fin n → ℂ) → (Fin k × Fin n → ℂ) := fun v p => (Sᵀ *ᵥ v p.1) p.2
  let Bc : Set (Fin n → ℂ) := {u | IndefiniteRowSideFullHecke.ArithBezout.normSq u ≤ 1}
  let BC : Set (Fin k × Fin n → ℂ) :=
    MeasurableEquiv.curry (Fin k) (Fin n) ℂ ⁻¹' Set.univ.pi fun _ => Bc
  let BA : Set (Fin k × Fin n → ℂ) := {u | ∀ i, IndefiniteRowSideFullHecke.ArithBezout.formNorm S (fun j => u (i, j)) < 1}

  have hNf : Measurable Nf := by
    refine measurable_pi_lambda _ fun ij => ?_
    exact ((Complex.measurable_ofReal.comp ((continuous_formNorm S).comp
      (continuous_pi fun j => continuous_apply (ij.1, j))).measurable).inv).mul
      (measurable_pi_apply ij)
  have hR : Measurable R :=
    ((continuous_normSq.sqrt).measurable.inv).smul measurable_id
  have hT : Measurable T := by
    refine (continuous_pi fun p => ?_).measurable
    exact (continuous_apply p.2).comp
      (Continuous.matrix_mulVec continuous_const (continuous_apply p.1))

  have hBc : MeasurableSet Bc := measurableSet_le continuous_normSq.measurable measurable_const
  have hBc0 : (volume : Measure (Fin n → ℂ)) Bc ≠ 0 := by
    have hO : IsOpen {u : Fin n → ℂ | IndefiniteRowSideFullHecke.ArithBezout.normSq u < 1} :=
      isOpen_lt continuous_normSq continuous_const
    have hne : ({u : Fin n → ℂ | IndefiniteRowSideFullHecke.ArithBezout.normSq u < 1}).Nonempty :=
      ⟨0, by simp [IndefiniteRowSideFullHecke.ArithBezout.normSq]⟩
    exact (lt_of_lt_of_le (hO.measure_pos volume hne)
      (measure_mono (Set.ofPred_subset_ofPred.mpr fun _ h => h.le))).ne'
  have hBctop : (volume : Measure (Fin n → ℂ)) Bc ≠ ⊤ := by
    have hcl : IsClosed Bc := isClosed_le continuous_normSq continuous_const
    have hbd : Bornology.IsBounded Bc := by
      rw [Metric.isBounded_iff_subset_closedBall 0]
      refine ⟨1, fun v hv => ?_⟩
      have hv' : IndefiniteRowSideFullHecke.ArithBezout.normSq v ≤ 1 := hv
      rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
      intro i
      have h1 : ‖v i‖ ^ 2 ≤ IndefiniteRowSideFullHecke.ArithBezout.normSq v :=
        Finset.single_le_sum (f := fun i => ‖v i‖ ^ 2) (fun _ _ => by positivity)
          (Finset.mem_univ i)
      nlinarith [norm_nonneg (v i), hv']
    exact (Metric.isCompact_of_isClosed_isBounded hcl hbd).measure_lt_top.ne
  have : IsProbabilityMeasure (cond (volume : Measure (Fin n → ℂ)) Bc) :=
    cond_isProbabilityMeasure_of_finite hBc0 hBctop

  have hB : IndefiniteRowSideFullHecke.ArithBezout.formSphereLaw S k =
      (cond (volume : Measure (Fin k × Fin n → ℂ)) BC).map
        (T ∘ (fun v i => R (v i)) ∘ MeasurableEquiv.curry (Fin k) (Fin n) ℂ) := by
    have h1 : IndefiniteRowSideFullHecke.ArithBezout.sphereLaw n = (cond volume Bc).map R := rfl
    have : ∀ _ : Fin k, SigmaFinite ((cond (volume : Measure (Fin n → ℂ)) Bc).map R) :=
      fun _ => by
        have := Measure.isProbabilityMeasure_map (μ := cond (volume : Measure (Fin n → ℂ)) Bc)
          hR.aemeasurable
        infer_instance
    have h2 : Measure.pi (fun _ : Fin k => IndefiniteRowSideFullHecke.ArithBezout.sphereLaw n) =
        (Measure.pi fun _ : Fin k => cond (volume : Measure (Fin n → ℂ)) Bc).map
          (fun v i => R (v i)) := by
      rw [h1, Measure.pi_map_pi fun _ => hR.aemeasurable]
    have h3 : Measure.pi (fun _ : Fin k => cond (volume : Measure (Fin n → ℂ)) Bc) =
        (cond (volume : Measure (Fin k × Fin n → ℂ)) BC).map
          (MeasurableEquiv.curry (Fin k) (Fin n) ℂ) := by
      rw [cond_map_equiv, map_curry_volume]
      refine Measure.pi_eq fun s hs => ?_
      rw [cond_apply (MeasurableSet.univ_pi fun _ => hBc), Measure.pi_pi,
        ← Set.pi_inter_distrib, Measure.pi_pi]
      simp_rw [cond_apply hBc]
      rw [Finset.prod_mul_distrib, ENNReal.prod_inv_distrib]
      exact fun _ _ _ _ _ => Or.inr hBctop
    have hRk : Measurable fun (v : Fin k → Fin n → ℂ) i => R (v i) :=
      measurable_pi_lambda _ fun i => hR.comp (measurable_pi_apply i)
    rw [IndefiniteRowSideFullHecke.ArithBezout.formSphereLaw, h2, h3, Measure.map_map hRk (MeasurableEquiv.measurable _),
      Measure.map_map hT (hRk.comp (MeasurableEquiv.measurable _))]

  have hA : sphereMean h k g = ∫ u, g (Nf u) ∂cond volume BA := by
    unfold sphereMean
    rw [hN]
    simp only [MeasureTheory.average, Measure.restrict_apply_univ]
    rfl

  have hc := Measure.map_linearMap_addHaar_eq_smul_addHaar
    (μ := (volume : Measure (Fin k × Fin n → ℂ))) (f := E.toLinearMap) E.isUnit_det'.ne_zero
  have hcF : (volume : Measure (Fin k × Fin n → ℂ)).map F =
      ENNReal.ofReal |(LinearMap.det E.toLinearMap)⁻¹| • volume := by
    have hFE : ⇑F = ⇑E.toLinearMap := by
      funext x
      rfl
    rw [hFE]
    exact hc
  have hc0 : ENNReal.ofReal |(LinearMap.det E.toLinearMap)⁻¹| ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact abs_pos.mpr (inv_ne_zero E.isUnit_det'.ne_zero)
  have hmem : ∀ w, w ∈ F ⁻¹' BA ↔ ∀ i, IndefiniteRowSideFullHecke.ArithBezout.normSq (fun j => w (i, j)) < 1 := by
    intro w
    simp only [Set.mem_preimage, BA, Set.mem_ofPred_eq, hF]
    refine forall_congr' fun i => ?_
    rw [show (fun j => blockMul Sᵀ w (i, j)) = Sᵀ *ᵥ fun j => w (i, j) from rfl,
      formNorm_transpose_mulVec hS, Real.sqrt_lt' one_pos, one_pow]
  have hmemC : ∀ w, w ∈ BC ↔ ∀ i, IndefiniteRowSideFullHecke.ArithBezout.normSq (fun j => w (i, j)) ≤ 1 := by
    intro w
    simp only [BC, Bc, Set.mem_preimage, Set.mem_univ_pi]
    rfl
  have hnull : ∀ i : Fin k, (volume : Measure (Fin k × Fin n → ℂ))
      {w | IndefiniteRowSideFullHecke.ArithBezout.normSq (fun j => w (i, j)) = 1} = 0 := by
    intro i
    have h1 := Measure.pi_eval_preimage_null (fun _ : Fin k => (volume : Measure (Fin n → ℂ)))
      (i := i) volume_normSq_eq_one
    rw [← map_curry_volume, MeasurableEquiv.map_apply] at h1
    exact h1
  have hpre : F ⁻¹' BA =ᵐ[volume] BC := by
    refine ae_eq_set.mpr ⟨?_, ?_⟩
    · rw [Set.sdiff_eq_empty.mpr fun w hw => (hmemC w).mpr fun i => ((hmem w).mp hw i).le,
        measure_empty]
    · refine measure_mono_null (fun w hw => ?_) (measure_iUnion_null hnull)
      obtain ⟨hC, hA'⟩ := hw
      rw [hmem] at hA'
      push Not at hA'
      obtain ⟨i, hi⟩ := hA'
      exact Set.mem_iUnion.mpr ⟨i, le_antisymm ((hmemC w).mp hC i) hi⟩
  have hpt : ∀ w, Nf (F w) = (T ∘ (fun v i => R (v i)) ∘ MeasurableEquiv.curry (Fin k) (Fin n) ℂ) w := by
    intro w
    funext ij
    show ((IndefiniteRowSideFullHecke.ArithBezout.formNorm S (fun j => blockMul Sᵀ w (ij.1, j)) : ℝ) : ℂ)⁻¹ *
        blockMul Sᵀ w ij =
      (Sᵀ *ᵥ ((√(IndefiniteRowSideFullHecke.ArithBezout.normSq fun j => w (ij.1, j)))⁻¹ • fun j => w (ij.1, j))) ij.2
    rw [show (fun j => blockMul Sᵀ w (ij.1, j)) = Sᵀ *ᵥ fun j => w (ij.1, j) from rfl,
      formNorm_transpose_mulVec hS, mulVec_smul, Pi.smul_apply, Complex.real_smul,
      Complex.ofReal_inv]
    rfl
  have hmeas : Measurable (T ∘ (fun v i => R (v i)) ∘ MeasurableEquiv.curry (Fin k) (Fin n) ℂ) :=
    hT.comp ((measurable_pi_lambda _ fun i => hR.comp (measurable_pi_apply i)).comp
      (MeasurableEquiv.measurable _))
  calc sphereMean h k g = ∫ u, g (Nf u) ∂cond volume BA := hA
    _ = ∫ u, g (Nf u) ∂cond (volume.map F) BA := by
      rw [hcF, cond_smul _ _ hc0 ENNReal.ofReal_ne_top]
    _ = ∫ u, g (Nf u) ∂(cond volume (F ⁻¹' BA)).map F := by rw [cond_map_equiv]
    _ = ∫ u, g (Nf u) ∂(cond volume BC).map F := by rw [cond_congr_set _ hpre]
    _ = ∫ w, g (Nf (F w)) ∂cond volume BC :=
      integral_map F.measurable.aemeasurable (hg.comp hNf).aestronglyMeasurable
    _ = ∫ w, g ((T ∘ (fun v i => R (v i)) ∘ MeasurableEquiv.curry (Fin k) (Fin n) ℂ) w)
          ∂cond volume BC := by
      simp_rw [hpt]
    _ = ∫ u, g u ∂IndefiniteRowSideFullHecke.ArithBezout.formSphereLaw S k := by
      rw [hB, integral_map hmeas.aemeasurable hg.aestronglyMeasurable]

theorem mahler_eq_chowMean (S : Matrix (Fin n) (Fin n) ℂ) (hS : IsUnit S) (h : HermNorm n)
    (hh : ∀ u, h.norm u = IndefiniteRowSideFullHecke.ArithBezout.formNorm S u) (f : MvPolynomial (Fin k × Fin n) ℂ) :
    mahler h k f = IndefiniteRowSideFullHecke.ArithBezout.chowMean S k f :=
  sphereMean_eq_integral S hS h hh _
    (Real.measurable_log.comp (continuous_norm.comp (MvPolynomial.continuous_eval f)).measurable)

theorem gaussNorm_eq_coeffGaussNorm {K : Type*} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) {ι : Type*} (f : MvPolynomial ι K) :
    gaussNorm v f = ReciprocityTheory.ChartRestriction.G.Geo.coeffGaussNorm (HeightOneSpectrum.adicAbv K v) f := by
  classical
  unfold gaussNorm ReciprocityTheory.ChartRestriction.G.Geo.coeffGaussNorm
  rcases f.support.eq_empty_or_nonempty with h | h
  · have : IsEmpty f.support := by rw [h]; infer_instance
    simp only [h, Real.iSup_of_isEmpty]
    rfl
  · have : Nonempty f.support := h.to_subtype
    have hb : BddAbove (Set.range fun m : f.support => HeightOneSpectrum.adicAbv K v (f.coeff m)) :=
      (Set.finite_range _).bddAbove
    apply le_antisymm
    · obtain ⟨m, hm, hmax⟩ := Finset.exists_max_image f.support
        (fun m => HeightOneSpectrum.adicAbv K v (f.coeff m)) h
      refine le_trans ?_ (le_ciSup hb ⟨m, hm⟩)
      have hle : f.support.sup (fun m => (⟨HeightOneSpectrum.adicAbv K v (f.coeff m),
          AbsoluteValue.nonneg _ _⟩ : NNReal)) ≤
          ⟨HeightOneSpectrum.adicAbv K v (f.coeff m), AbsoluteValue.nonneg _ _⟩ :=
        Finset.sup_le fun b hb => hmax b hb
      exact NNReal.coe_le_coe.mpr hle
    · refine ciSup_le fun m => ?_
      have hle := Finset.le_sup (f := fun m => (⟨HeightOneSpectrum.adicAbv K v (f.coeff m),
          AbsoluteValue.nonneg _ _⟩ : NNReal)) m.2
      exact NNReal.coe_le_coe.mpr hle

theorem finsum_log_gaussNorm {K : Type*} [Field K] [NumberField K] {ι : Type*}
    (f : MvPolynomial ι K) :
    ∑ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K), Real.log (gaussNorm v f) =
      ∑ᶠ v : Height.AdmissibleAbsValues.nonarchAbsVal (K := K),
        Real.log (ReciprocityTheory.ChartRestriction.G.Geo.coeffGaussNorm v.1 f) := by
  have hv : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      (FinitePlace.equivHeightOneSpectrum.symm v : FinitePlace K).val =
        HeightOneSpectrum.adicAbv K v := fun v => by
    ext x
    exact FinitePlace.norm_embedding v x
  show _ = ∑ᶠ w : FinitePlace K, Real.log (ReciprocityTheory.ChartRestriction.G.Geo.coeffGaussNorm w.val f)
  rw [← finsum_comp_equiv (FinitePlace.equivHeightOneSpectrum (K := K)).symm]
  simp_rw [hv, gaussNorm_eq_coeffGaussNorm]

theorem finGaussLog_eq {ι : Type*} (f : MvPolynomial ι ℚ) :
    IndefiniteRowSideFullHecke.ArithBezout.finGaussLog f =
      ∑ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ), Real.log (gaussNorm v f) :=
  (finsum_log_gaussNorm f).symm

theorem chowHt_eq_chowHeight {e δ : ℕ} (H : ArchData ℚ n) (S : Matrix (Fin n) (Fin n) ℂ)
    (hS : IsUnit S) (hH : ∀ σ u, (H.normAt σ).norm u = IndefiniteRowSideFullHecke.ArithBezout.formNorm S u)
    (f : MvPolynomial (Fin (e + 1) × Fin n) ℚ) :
    chowHt H (e + 1) δ f = IndefiniteRowSideFullHecke.ArithBezout.chowHeight S f δ := by
  have hσ : ∀ σ : ℚ →+* ℂ, σ = Rat.castHom ℂ := fun σ => Subsingleton.elim _ _
  have hw : Height.totalWeight ℚ = 1 := by
    rw [NumberField.totalWeight_eq_finrank, Module.finrank_self]
  have hmult : (default : InfinitePlace ℚ).mult = 1 := by
    have := NumberField.totalWeight_eq_sum_mult (K := ℚ)
    rw [hw, Fintype.sum_unique] at this
    exact this.symm
  unfold chowHt IndefiniteRowSideFullHecke.ArithBezout.chowHeight ReciprocityTheory.ChartRestriction.G.Geo.chowHt ReciprocityTheory.ChartRestriction.G.Geo.chowHeightOfForm
  rw [finsum_log_gaussNorm, Fintype.sum_subsingleton _ (Rat.castHom ℂ), Fintype.sum_unique,
    hmult, hw, hσ (default : InfinitePlace ℚ).embedding, Module.finrank_self,
    mahler_eq_chowMean S hS _ (hH _)]
  simp only [ReciprocityTheory.ChartRestriction.G.Geo.logMean, IndefiniteRowSideFullHecke.ArithBezout.chowMean]
  push_cast
  ring

theorem continuous_hermNorm (h : HermNorm n) : Continuous h.norm := by
  obtain ⟨S, hS, rfl⟩ := exists_eq_ofPointMatrix h
  rw [show (ofPointMatrix S hS).norm = IndefiniteRowSideFullHecke.ArithBezout.formNorm S from
    funext (ofPointMatrix_norm S hS)]
  exact continuous_formNorm S

theorem integral_cond_linearEquiv (E : (Fin k × Fin n → ℂ) ≃ₗ[ℝ] (Fin k × Fin n → ℂ))
    (s : Set (Fin k × Fin n → ℂ)) (G : (Fin k × Fin n → ℂ) → ℝ) (hG : Measurable G) :
    ∫ u, G (E u) ∂cond volume (E ⁻¹' s) = ∫ x, G x ∂cond volume s := by
  let F : (Fin k × Fin n → ℂ) ≃ᵐ (Fin k × Fin n → ℂ) :=
    E.toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv
  have hFE : ⇑F = ⇑E.toLinearMap := by
    funext x
    rfl
  have hc := Measure.map_linearMap_addHaar_eq_smul_addHaar
    (μ := (volume : Measure (Fin k × Fin n → ℂ))) (f := E.toLinearMap) E.isUnit_det'.ne_zero
  have hc0 : ENNReal.ofReal |(LinearMap.det E.toLinearMap)⁻¹| ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact abs_pos.mpr (inv_ne_zero E.isUnit_det'.ne_zero)
  show ∫ u, G (F u) ∂cond volume (F ⁻¹' s) = _
  rw [← integral_map F.measurable.aemeasurable hG.aestronglyMeasurable, cond_map_equiv, hFE, hc,
    cond_smul _ _ hc0 ENNReal.ofReal_ne_top]

theorem eval_map_conjugate {K : Type*} [Field K] {ι : Type*} (σ : K →+* ℂ)
    (f : MvPolynomial ι K) (x : ι → ℂ) :
    eval x (f.map (ComplexEmbedding.conjugate σ)) =
      starRingEnd ℂ (eval (star x) (f.map σ)) := by
  rw [eval_map, eval_map, eval₂_comp_left]
  congr 1
  funext i
  simp

theorem mahler_conjugate {K : Type*} [Field K] (h h' : HermNorm n)
    (hc : ∀ u, h'.norm (star u) = h.norm u) (σ : K →+* ℂ) (f : MvPolynomial (Fin k × Fin n) K) :
    mahler h' k (f.map (ComplexEmbedding.conjugate σ)) = mahler h k (f.map σ) := by
  have hc' : ∀ u, h'.norm u = h.norm (star u) := fun u => by rw [← hc, star_star]
  let Cj : (Fin k × Fin n → ℂ) ≃ₗ[ℝ] (Fin k × Fin n → ℂ) :=
    LinearEquiv.piCongrRight fun _ => Complex.conjAe.toLinearEquiv
  have hCj : ∀ u, Cj u = star u := fun u => rfl
  let N : (Fin k × Fin n → ℂ) → (Fin k × Fin n → ℂ) := fun u ij =>
    ((h.norm fun j => u (ij.1, j) : ℝ) : ℂ)⁻¹ * u ij
  let G : (Fin k × Fin n → ℂ) → ℝ := fun u => Real.log ‖eval (N u) (f.map σ)‖
  have hN : Measurable N := by
    refine measurable_pi_lambda _ fun ij => ?_
    exact ((Complex.measurable_ofReal.comp ((continuous_hermNorm h).comp
      (continuous_pi fun j => continuous_apply (ij.1, j))).measurable).inv).mul
      (measurable_pi_apply ij)
  have hG : Measurable G :=
    Real.measurable_log.comp ((continuous_norm.comp (continuous_eval _)).measurable.comp hN)
  have hset : {u : Fin k × Fin n → ℂ | ∀ i, h'.norm (fun j => u (i, j)) < 1} =
      Cj ⁻¹' {u | ∀ i, h.norm (fun j => u (i, j)) < 1} := by
    ext u
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, hCj, hc']
    rfl
  have hpt : ∀ u : Fin k × Fin n → ℂ,
      Real.log ‖eval (fun ij => ((h'.norm fun j => u (ij.1, j) : ℝ) : ℂ)⁻¹ * u ij)
        (f.map (ComplexEmbedding.conjugate σ))‖ = G (Cj u) := by
    intro u
    have hNs : N (Cj u) = star fun ij => ((h'.norm fun j => u (ij.1, j) : ℝ) : ℂ)⁻¹ * u ij := by
      funext ij
      have h1 : h'.norm (fun j => u (ij.1, j)) = h.norm (fun j => star (u (ij.1, j))) :=
        hc' _
      simp only [N, hCj, Pi.star_apply]
      rw [← h1, star_mul', star_inv₀, Complex.star_def, Complex.conj_ofReal]
    simp only [G, hNs, eval_map_conjugate, Complex.norm_conj]
  unfold mahler sphereMean
  simp only [MeasureTheory.average, Measure.restrict_apply_univ]
  show ∫ u, Real.log ‖eval (fun ij => ((h'.norm fun j => u (ij.1, j) : ℝ) : ℂ)⁻¹ * u ij)
        (f.map (ComplexEmbedding.conjugate σ))‖
      ∂cond volume {u : Fin k × Fin n → ℂ | ∀ i, h'.norm (fun j => u (i, j)) < 1} =
    ∫ u, G u ∂cond volume {u : Fin k × Fin n → ℂ | ∀ i, h.norm (fun j => u (i, j)) < 1}
  simp_rw [hpt, hset]
  exact integral_cond_linearEquiv Cj _ G hG

theorem sum_embeddings_eq {K : Type*} [Field K] [NumberField K] (F : (K →+* ℂ) → ℝ)
    (hF : ∀ σ, F (ComplexEmbedding.conjugate σ) = F σ) :
    ∑ σ, F σ = ∑ w : InfinitePlace K, (w.mult : ℝ) * F w.embedding := by
  classical
  rw [← Finset.univ.sum_fiberwise (fun σ => InfinitePlace.mk σ) F]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Finset.sum_congr rfl (g := fun _ => F w.embedding) ?_, Finset.sum_const,
    InfinitePlace.card_filter_mk_eq, nsmul_eq_mul]
  intro σ hσ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ
  rw [← InfinitePlace.mk_embedding w, InfinitePlace.mk_eq_iff] at hσ
  rcases hσ with rfl | hσ
  · rfl
  · rw [← hσ, hF]

theorem chowHt_eq_chowHt_places {K : Type} [Field K] [NumberField K] {e δ : ℕ} (H : ArchData K n)
    (S : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (hS : ∀ w, IsUnit (S w))
    (hH : ∀ w u, (H.normAt w.embedding).norm u = IndefiniteRowSideFullHecke.ArithBezout.formNorm (S w) u)
    (f : MvPolynomial (Fin (e + 1) × Fin n) K) :
    chowHt H (e + 1) δ f =
      ReciprocityTheory.ChartRestriction.G.Geo.chowHt (fun w => IndefiniteRowSideFullHecke.ArithBezout.formSphereLaw (S w) (e + 1)) f δ := by
  have hsum := sum_embeddings_eq (fun σ => mahler (H.normAt σ) (e + 1) (f.map σ))
    fun σ => mahler_conjugate _ _ (H.conj_norm σ) σ f
  have hm : ∀ w : InfinitePlace K, mahler (H.normAt w.embedding) (e + 1) (f.map w.embedding) =
      ReciprocityTheory.ChartRestriction.G.Geo.logMean (IndefiniteRowSideFullHecke.ArithBezout.formSphereLaw (S w) (e + 1))
        (MvPolynomial.map w.embedding f) :=
    fun w => mahler_eq_chowMean (S w) (hS w) _ (hH w) _
  have hd : (Module.finrank ℚ K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
  unfold chowHt ReciprocityTheory.ChartRestriction.G.Geo.chowHt ReciprocityTheory.ChartRestriction.G.Geo.chowHeightOfForm
  rw [finsum_log_gaussNorm, Finset.sum_add_distrib, hsum, Finset.sum_const, Finset.card_univ,
    NumberField.Embeddings.card K ℂ, NumberField.totalWeight_eq_finrank, nsmul_eq_mul]
  simp_rw [hm]
  field_simp
  push_cast
  ring

theorem equiv :
    (∀ (n : ℕ) (S : Matrix (Fin n) (Fin n) ℂ) (hS : IsUnit S),
      (∀ u, (ofPointMatrix S hS).norm u = IndefiniteRowSideFullHecke.ArithBezout.formNorm S u) ∧
      (∀ y, (ofPointMatrix S hS).dualNorm y = (IndefiniteRowSideFullHecke.ArithBezout.pointMetric S hS).ρ y) ∧
      (∀ u y, fsLog (ofPointMatrix S hS) u y =
        IndefiniteRowSideFullHecke.ArithBezout.logFormNorm S hS u (fun p => y p.2))) ∧
    (∀ (n : ℕ) (h : HermNorm n), ∃ (S : Matrix (Fin n) (Fin n) ℂ) (hS : IsUnit S),
      h = ofPointMatrix S hS) ∧
    (∀ n : ℕ, HermNorm.std n = ofPointMatrix 1 isUnit_one) ∧
    (∀ (n k : ℕ) (S : Matrix (Fin n) (Fin n) ℂ), IsUnit S → ∀ h : HermNorm n,
      (∀ u, h.norm u = IndefiniteRowSideFullHecke.ArithBezout.formNorm S u) →
        (∀ g : (Fin k × Fin n → ℂ) → ℝ, Measurable g →
          sphereMean h k g = ∫ u, g u ∂IndefiniteRowSideFullHecke.ArithBezout.formSphereLaw S k) ∧
        ∀ f : MvPolynomial (Fin k × Fin n) ℂ, mahler h k f = IndefiniteRowSideFullHecke.ArithBezout.chowMean S k f) ∧
    (∀ (K : Type) [Field K] [NumberField K] (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
      (ι : Type) (f : MvPolynomial ι K),
      gaussNorm v f = ReciprocityTheory.ChartRestriction.G.Geo.coeffGaussNorm (HeightOneSpectrum.adicAbv K v) f) ∧
    (∀ (K : Type) [Field K] [NumberField K] (ι : Type) (f : MvPolynomial ι K),
      ∑ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K), Real.log (gaussNorm v f) =
        ∑ᶠ v : Height.AdmissibleAbsValues.nonarchAbsVal (K := K),
          Real.log (ReciprocityTheory.ChartRestriction.G.Geo.coeffGaussNorm v.1 f)) ∧
    (∀ (ι : Type) (f : MvPolynomial ι ℚ), IndefiniteRowSideFullHecke.ArithBezout.finGaussLog f =
      ∑ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ), Real.log (gaussNorm v f)) ∧
    (∀ (n e δ : ℕ) (H : ArchData ℚ n) (S : Matrix (Fin n) (Fin n) ℂ), IsUnit S →
      (∀ σ u, (H.normAt σ).norm u = IndefiniteRowSideFullHecke.ArithBezout.formNorm S u) →
        ∀ f : MvPolynomial (Fin (e + 1) × Fin n) ℚ,
          chowHt H (e + 1) δ f = IndefiniteRowSideFullHecke.ArithBezout.chowHeight S f δ) ∧
    (∀ (K : Type) [Field K] [NumberField K] (n e δ : ℕ) (H : ArchData K n)
      (S : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ), (∀ w, IsUnit (S w)) →
      (∀ w u, (H.normAt w.embedding).norm u = IndefiniteRowSideFullHecke.ArithBezout.formNorm (S w) u) →
        ∀ f : MvPolynomial (Fin (e + 1) × Fin n) K,
          chowHt H (e + 1) δ f =
            ReciprocityTheory.ChartRestriction.G.Geo.chowHt (fun w => IndefiniteRowSideFullHecke.ArithBezout.formSphereLaw (S w) (e + 1)) f δ) :=
  ⟨fun _ S hS => ⟨ofPointMatrix_norm S hS, ofPointMatrix_dualNorm S hS, ofPointMatrix_fsLog S hS⟩,
    fun _ h => exists_eq_ofPointMatrix h,
    fun _ => std_eq_ofPointMatrix_one,
    fun _ _ S hS h hh => ⟨fun g hg => sphereMean_eq_integral S hS h hh g hg,
      fun f => mahler_eq_chowMean S hS h hh f⟩,
    fun _ _ _ v _ f => gaussNorm_eq_coeffGaussNorm v f,
    fun _ _ _ _ f => finsum_log_gaussNorm f,
    fun _ f => finGaussLog_eq f,
    fun _ _ _ H S hS hH f => chowHt_eq_chowHeight H S hS hH f,
    fun _ _ _ _ _ _ H S hS hH f => chowHt_eq_chowHt_places H S hS hH f⟩

end ObjectsHeight

end

end GroundTheory.Heights₂.Heights
