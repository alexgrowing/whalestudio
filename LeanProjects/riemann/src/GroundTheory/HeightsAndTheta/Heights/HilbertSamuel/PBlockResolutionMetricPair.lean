import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBlockResolutionMetricPair
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBergmanDensChartSum
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.AnResBridgePot
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
import ReciprocityTheory.AnalyticForms.PotentialTheory.LocDens
import ReciprocityTheory.AnalyticForms.PotentialTheory.AtlasIndep
import ReciprocityTheory.AnalyticForms.PotentialTheory.IntegrableOnTargetOfTsupport
import ReciprocityTheory.AnalyticForms.PotentialTheory.Partition
import ReciprocityTheory.AnalyticForms.PotentialTheory.HessCIsHermitian
import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffAtOfIsPotential
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.MdiscSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ADensStC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ABridgeStA
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M MeasureTheory Filter
  Topology Set
open scoped ContDiff ENNReal

noncomputable section

set_option linter.unusedSectionVars false

namespace BlockResolutionMetricPair

section Refine

variable {e : ℕ} {X : Type} [TopologicalSpace X]

abbrev refine (A : FinHolAtlas e X) {m : ℕ} (j : Fin m → Fin A.n) (V : Fin m → Set X)
    (hV : ∀ i, IsOpen (V i)) (hcov : ∀ x, ∃ i, x ∈ (A.chart (j i)).source ∩ V i) : FinHolAtlas e X where
  n := m
  chart i := (A.chart (j i)).restrOpen (V i) (hV i)
  cover := hcov
  holo i k := (A.holo (j i) (j k)).mono fun _ hy => ⟨hy.1.1, hy.2.1⟩

variable (A : FinHolAtlas e X) {m : ℕ} (j : Fin m → Fin A.n) (V : Fin m → Set X)
    (hV : ∀ i, IsOpen (V i)) (hcov : ∀ x, ∃ i, x ∈ (A.chart (j i)).source ∩ V i)

theorem mem_refine_source {i : Fin m} {x : X} :
    x ∈ ((refine A j V hV hcov).chart i).source ↔ x ∈ (A.chart (j i)).source ∧ x ∈ V i := Iff.rfl

theorem mem_refine_target {i : Fin m} {y : Fin e → ℂ} :
    y ∈ ((refine A j V hV hcov).chart i).target ↔ y ∈ (A.chart (j i)).target ∧ (A.chart (j i)).symm y ∈ V i :=
  Iff.rfl

theorem refine_compatible : (refine A j V hV hcov).Compatible A :=
  ⟨fun i k => (A.holo (j i) k).mono fun _ hy => ⟨hy.1.1, hy.2⟩,
    fun i k => (A.holo i (j k)).mono fun _ hy => ⟨hy.1, hy.2.1⟩⟩

theorem lintegral_chart [MeasurableSpace X] [BorelSpace X] (c : OpenPartialHomeomorph X (Fin e → ℂ))
    (μ : Measure X) (ν : (Fin e → ℂ) → ℝ) (hνc : ContinuousOn ν c.target)
    (hν : ∀ S : Set X, MeasurableSet S → S ⊆ c.source →
      μ S = ∫⁻ y in c.target ∩ c.symm ⁻¹' S, ENNReal.ofReal (ν y))
    {W : Set X} (hW : IsOpen W) (g : X → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ x in c.source ∩ W, g x ∂μ = ∫⁻ y in c.target ∩ c.symm ⁻¹' W, g (c.symm y) * ENNReal.ofReal (ν y) := by
  set T := c.target ∩ c.symm ⁻¹' W with hT
  have hTm : MeasurableSet T := (c.isOpen_inter_preimage_symm hW).measurableSet
  have hsymm : AEMeasurable c.symm (volume.restrict T) :=
    (c.continuousOn_symm.mono inter_subset_left).aemeasurable hTm
  have hdens : AEMeasurable (fun y => ENNReal.ofReal (ν y)) (volume.restrict T) :=
    ENNReal.measurable_ofReal.comp_aemeasurable ((hνc.mono inter_subset_left).aemeasurable hTm)
  have hsymm' : AEMeasurable c.symm ((volume.restrict T).withDensity fun y => ENNReal.ofReal (ν y)) :=
    hsymm.mono_ac (withDensity_absolutelyContinuous _ _)
  have hmeas : μ.restrict (c.source ∩ W) =
      ((volume.restrict T).withDensity fun y => ENNReal.ofReal (ν y)).map c.symm := by
    ext S hS
    rw [Measure.restrict_apply hS, Measure.map_apply_of_aemeasurable hsymm' hS, withDensity_apply',
      Measure.restrict_restrict' hTm,
      hν _ (hS.inter (c.open_source.inter hW).measurableSet) (inter_subset_right.trans inter_subset_left)]
    have hset : c.target ∩ c.symm ⁻¹' (S ∩ (c.source ∩ W)) = c.symm ⁻¹' S ∩ T := by
      ext y
      constructor
      · rintro ⟨hyt, hyS, -, hyW⟩
        exact ⟨hyS, hyt, hyW⟩
      · rintro ⟨hyS, hyt, hyW⟩
        exact ⟨hyt, hyS, c.map_target hyt, hyW⟩
    rw [hset]
  rw [hmeas, lintegral_map' hg.aemeasurable hsymm',
    lintegral_withDensity_eq_lintegral_mul₀ (g := fun a => g (c.symm a)) hdens (hg.comp_aemeasurable hsymm)]
  refine lintegral_congr fun y => ?_
  simp [mul_comm]

end Refine

section Torus

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem eval_torus {R : Type} [CommRing R] (φ : R →+* ℂ) {f : MvPolynomial (Σ k, ι k) R} {k₀ : K} {n : ℕ}
    (hf : IsMultiHomog f (blockDeg k₀ n)) (c : K → ℂ) (z : (Σ k, ι k) → ℂ) :
    eval (fun p => c p.1 * z p) (map φ f) = c k₀ ^ n * eval z (map φ f) := by
  rw [eval_eq', eval_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hdeg := hf m (support_map_subset _ _ hm)
  have hc : ∏ p : (Σ k, ι k), c p.1 ^ m p = c k₀ ^ n := by
    rw [Fintype.prod_sigma]
    simp_rw [Finset.prod_pow_eq_pow_sum, hdeg]
    rw [Fintype.prod_eq_single k₀ fun k hk => by simp [blockDeg, hk]]
    simp [blockDeg]
  simp_rw [mul_pow, Finset.prod_mul_distrib, hc]
  ring

theorem prod_norm_unitDeg (c : K → ℂ) (k₀ : K) : ∏ k, ‖c k‖ ^ unitDeg k₀ k = ‖c k₀‖ := by
  rw [Fintype.prod_eq_single k₀ fun k hk => by simp [unitDeg, hk]]
  simp [unitDeg]

omit [DecidableEq K] [∀ k, Fintype (ι k)] in

theorem isOpen_blockNonzero : IsOpen {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
  simp only [Set.ofPred_forall, Set.ofPred_exists]
  exact isOpen_iInter_of_finite fun k => isOpen_iUnion fun i =>
    isOpen_ne_fun (continuous_apply _) continuous_const

def blockRatio (k₀ : K) (z z' : (Σ k, ι k) → ℂ) : ℂ :=
  if h : ∃ i : ι k₀, z' ⟨k₀, i⟩ ≠ 0 then z ⟨k₀, h.choose⟩ / z' ⟨k₀, h.choose⟩ else 1

theorem blockRatio_eq {k₀ : K} {z' : (Σ k, ι k) → ℂ} (c : K → ℂ) (h : ∃ i : ι k₀, z' ⟨k₀, i⟩ ≠ 0) :
    blockRatio k₀ (fun p => c p.1 * z' p) z' = c k₀ := by
  rw [blockRatio, dif_pos h]
  exact mul_div_cancel_right₀ _ h.choose_spec

theorem blockRatio_eq_div {k₀ : K} {z z' : (Σ k, ι k) → ℂ} (hzz : SameOrbit z z') {i : ι k₀}
    (hi : z' ⟨k₀, i⟩ ≠ 0) : blockRatio k₀ z z' = z ⟨k₀, i⟩ / z' ⟨k₀, i⟩ := by
  obtain ⟨c, -, rfl⟩ := hzz
  rw [blockRatio_eq c ⟨i, hi⟩]
  exact (mul_div_cancel_right₀ _ hi).symm

theorem isConeTangent_of_map {P0 P : Ideal (MRing ι)} (hP0 : P0 ≤ P) {e : ℕ}
    {γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ} {y : Fin e → ℂ} (hγ : AnalyticAt ℂ γ y)
    (hpts : ∀ᶠ y' in 𝓝 y, γ y' ∈ mcPts P) (ξ : Fin e → ℂ) :
    IsConeTangent (Int.castRingHom ℂ) P0 (γ y) (fderiv ℂ γ y ξ) := by
  intro f hf
  set F := map (Int.castRingHom ℂ) f
  have hzero : (fun w => eval w F) ∘ γ =ᶠ[𝓝 y] fun _ => (0 : ℂ) := by
    filter_upwards [hpts] with w hw
    exact hw.2 f (hP0 hf)
  have hd := (adens_hasFDerivAt_eval F (γ y)).comp y hγ.differentiableAt.hasFDerivAt
  have h0 : HasFDerivAt ((fun w => eval w F) ∘ γ) (0 : (Fin e → ℂ) →L[ℂ] ℂ) y :=
    (hasFDerivAt_const (0 : ℂ) y).congr_of_eventuallyEq hzero
  have := congrArg (fun L => L ξ) (hd.unique h0)
  simpa [_root_.sum_apply, smul_eq_mul] using this

theorem levi_const_mul {κ : Type} [Fintype κ] {f : (κ → ℂ) → ℝ} {z : κ → ℂ} (c : ℝ)
    (hf : ContDiffAt ℝ 2 f z) (w : κ → ℂ) : levi (fun y => c * f y) z w = c * levi f z w := by
  have h := levi_add_smul (f := fun _ => (0 : ℝ)) c contDiffAt_const hf w
  simp only [zero_add] at h
  rw [h]
  simp [levi]

end Torus

section Datum

variable {D : ℕ} {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {Ω : Type} [Field Ω] [CharZero Ω] (d : HSMBlockDatum D K ι Ω)

def nbhd (x : d.R.X) : Set d.R.X := d.R.U x ∩ (d.R.A.chart (chartIdx d.R.A x)).source

theorem isOpen_nbhd (x : d.R.X) : IsOpen (nbhd d x) := (d.R.isOpen_U x).inter (d.R.A.chart _).open_source

theorem mem_nbhd (x : d.R.X) : x ∈ nbhd d x := ⟨d.R.mem_U x, Classical.choose_spec (d.R.A.cover x)⟩

theorem isPotential_blockInterpPot {A' : HermLine ι} (hA' : IsSmoothHerm A') (t : ℝ) :
    IsPotential d.R.A (blockInterpPot d d.A A' t) := by
  have h₀ := isPotentialRsmul d.R.A (1 - t) _ (AnResBridge.isPotential_potOf d.R d.semipos.1)
  have h₁ := isPotentialRsmul d.R.A t _ (AnResBridge.isPotential_potOf d.R hA')
  have hs := isPotentialAdd d.R.A _ _ h₀ h₁
  refine isPotential_mul d.R.A _ hs 1 _ ?_ fun x y => ?_
  · funext x
    exact (Set.inter_self _).symm
  · show _ = 1 * ((1 - t) * Real.log (d.A.h (d.R.lift x y)) + t * Real.log (A'.h (d.R.lift x y)))
    simp [blockInterpPot]

variable {r : ℕ} (pt : Fin r → d.R.X) (hcov : ∀ x, ∃ i, x ∈ nbhd d (pt i))

abbrev atlas : FinHolAtlas D d.R.X :=
  refine d.R.A (fun i => chartIdx d.R.A (pt i)) (fun i => d.R.U (pt i)) (fun i => d.R.isOpen_U (pt i))
    fun x => (hcov x).imp fun _ hx => ⟨hx.2, hx.1⟩

theorem mem_atlas_source {i : Fin r} {x : d.R.X} (hx : x ∈ ((atlas d pt hcov).chart i).source) :
    x ∈ d.R.U (pt i) :=
  ((mem_refine_source _ _ _ _ _).1 hx).2

theorem mem_atlas_target {i : Fin r} {y : Fin D → ℂ} (hy : y ∈ ((atlas d pt hcov).chart i).target) :
    y ∈ (d.R.A.chart (chartIdx d.R.A (pt i))).target ∧
      ((atlas d pt hcov).chart i).symm y ∈ d.R.U (pt i) :=
  (mem_refine_target _ _ _ _ _).1 hy

theorem sameOrbit_lift {i k : Fin r} {x : d.R.X} (hi : x ∈ ((atlas d pt hcov).chart i).source)
    (hk : x ∈ ((atlas d pt hcov).chart k).source) :
    SameOrbit (d.R.lift (pt i) x) (d.R.lift (pt k) x) :=
  d.R.compat _ _ x ⟨mem_atlas_source d pt hcov hi, mem_atlas_source d pt hcov hk⟩

theorem lift_mem {i : Fin r} {x : d.R.X} (hi : x ∈ ((atlas d pt hcov).chart i).source) :
    d.R.lift (pt i) x ∈ mcPts (mCoordIdeal d.y) :=
  d.R.mem _ x (mem_atlas_source d pt hcov hi)

theorem analyticAt_lift (i k : Fin r) {y : Fin D → ℂ} (hy : y ∈ ((atlas d pt hcov).chart k).target)
    (hU : ((atlas d pt hcov).chart k).symm y ∈ d.R.U (pt i)) :
    AnalyticAt ℂ (fun y p => d.R.lift (pt i) (((atlas d pt hcov).chart k).symm y) p) y :=
  analyticAt_pi_iff.2 fun p =>
    d.R.holo (pt i) p (chartIdx d.R.A (pt k)) y ⟨(mem_atlas_target d pt hcov hy).1, hU⟩

def bundle : HolLineBundle (atlas d pt hcov) where
  g i k x := blockRatio d.k₀ (d.R.lift (pt i) x) (d.R.lift (pt k) x)
  holo i k := by
    intro l y hy
    have hS : IsOpen (((atlas d pt hcov).chart l).target ∩ ((atlas d pt hcov).chart l).symm ⁻¹'
        (((atlas d pt hcov).chart i).source ∩ ((atlas d pt hcov).chart k).source)) :=
      ((atlas d pt hcov).chart l).isOpen_inter_preimage_symm
        (((atlas d pt hcov).chart i).open_source.inter ((atlas d pt hcov).chart k).open_source)
    obtain ⟨hyt, hyi, hyk⟩ := hy
    obtain ⟨p, hp⟩ := (lift_mem d pt hcov hyk).1 d.k₀
    have f1 := analyticAt_pi_iff.1 (analyticAt_lift d pt hcov i l hyt (mem_atlas_source d pt hcov hyi))
      ⟨d.k₀, p⟩
    have f2 := analyticAt_pi_iff.1 (analyticAt_lift d pt hcov k l hyt (mem_atlas_source d pt hcov hyk))
      ⟨d.k₀, p⟩
    refine (f1.div f2 hp).congr ?_
    filter_upwards [hS.mem_nhds ⟨hyt, hyi, hyk⟩, f2.continuousAt.eventually_ne hp] with y' hy' hne
    exact (blockRatio_eq_div (sameOrbit_lift d pt hcov hy'.2.1 hy'.2.2) hne).symm
  ne_zero i k x hx := by
    obtain ⟨c, hc, hz⟩ := sameOrbit_lift d pt hcov hx.1 hx.2
    show blockRatio d.k₀ (d.R.lift (pt i) x) (d.R.lift (pt k) x) ≠ 0
    rw [hz, blockRatio_eq c ((lift_mem d pt hcov hx.2).1 d.k₀)]
    exact hc _
  cocycle i k l x hx := by
    obtain ⟨⟨hi, hk⟩, hl⟩ := hx
    obtain ⟨p, hp⟩ := (lift_mem d pt hcov hl).1 d.k₀
    have hkl := sameOrbit_lift d pt hcov hk hl
    have hkp : d.R.lift (pt k) x ⟨d.k₀, p⟩ ≠ 0 := by
      obtain ⟨c, hc, hz⟩ := hkl
      rw [hz]
      exact mul_ne_zero (hc _) hp
    show blockRatio d.k₀ (d.R.lift (pt i) x) (d.R.lift (pt l) x) =
      blockRatio d.k₀ (d.R.lift (pt i) x) (d.R.lift (pt k) x) * blockRatio d.k₀ (d.R.lift (pt k) x) (d.R.lift (pt l) x)
    rw [blockRatio_eq_div (sameOrbit_lift d pt hcov hi hl) hp,
      blockRatio_eq_div (sameOrbit_lift d pt hcov hi hk) hkp, blockRatio_eq_div hkl hp]
    field_simp

theorem contDiffAt_weight (A : HermLine ι) (hs : IsSmoothHerm A) (i l : Fin r) {y : Fin D → ℂ}
    (hy : y ∈ ((atlas d pt hcov).chart l).target) (hU : ((atlas d pt hcov).chart l).symm y ∈ d.R.U (pt i)) :
    ContDiffAt ℝ ∞ (fun y => 2 * Real.log (A.h (d.R.lift (pt i) (((atlas d pt hcov).chart l).symm y)))) y := by
  have hG := analyticAt_lift d pt hcov i l hy hU
  have hmem := d.R.mem (pt i) _ hU
  have hh : ContDiffAt ℝ ∞ A.h (d.R.lift (pt i) (((atlas d pt hcov).chart l).symm y)) :=
    hs.contDiffAt (isOpen_blockNonzero.mem_nhds hmem.1)
  have hu : ContDiffAt ℝ ∞ (fun z => 2 * Real.log (A.h z))
      (d.R.lift (pt i) (((atlas d pt hcov).chart l).symm y)) :=
    contDiffAt_const.mul (hh.log (A.pos _ hmem.1).ne')
  have := hu.comp y (hG.contDiffAt.restrict_scalars ℝ)
  exact this

def weight (A : HermLine ι) (hA : A.a = unitDeg d.k₀) (hs : IsSmoothHerm A) : Weight (bundle d pt hcov) where
  φ i x := 2 * Real.log (A.h (d.R.lift (pt i) x))
  smooth i l := fun y hy =>
    (contDiffAt_weight d pt hcov A hs i l hy.1 (mem_atlas_source d pt hcov hy.2)).contDiffWithinAt
  compat i k x hx := by
    obtain ⟨c, hc, hz⟩ := sameOrbit_lift d pt hcov hx.1 hx.2
    have hk := lift_mem d pt hcov hx.2
    simp only [bundle]
    rw [hz, blockRatio_eq c (hk.1 d.k₀), A.smul c _ hc, hA, prod_norm_unitDeg]
    have h1 : 0 < A.h (d.R.lift (pt k) x) := A.pos _ hk.1
    have h2 : 0 < ‖c d.k₀‖ := norm_pos_iff.2 (hc _)
    rw [Real.log_mul h2.ne' h1.ne', Real.log_pow]
    push_cast
    ring

theorem weight_isSemipositive (A : HermLine ι) (hA : A.a = unitDeg d.k₀) (P0 : Ideal (MRing ι))
    (hP0 : P0 ≤ mCoordIdeal d.y) (hsp : IsSemipositiveRel P0 (mCoordIdeal d.y) A) :
    (weight d pt hcov A hA hsp.1).IsSemipositive := by
  intro l y hy w
  have hU := (mem_atlas_target d pt hcov hy).2
  have hG := analyticAt_lift d pt hcov l l hy hU
  have hmem := d.R.mem (pt l) _ hU
  have hh : ContDiffAt ℝ 2 A.h (d.R.lift (pt l) (((atlas d pt hcov).chart l).symm y)) :=
    (hsp.1.contDiffAt (isOpen_blockNonzero.mem_nhds hmem.1)).of_le (WithTop.coe_le_coe.2 le_top)
  have hlog : ContDiffAt ℝ 2 (fun z => Real.log (A.h z))
      (d.R.lift (pt l) (((atlas d pt hcov).chart l).symm y)) := hh.log (A.pos _ hmem.1).ne'
  have hpts : ∀ᶠ y' in 𝓝 y,
      (fun y p => d.R.lift (pt l) (((atlas d pt hcov).chart l).symm y) p) y' ∈ mcPts (mCoordIdeal d.y) := by
    filter_upwards [((atlas d pt hcov).chart l).open_target.mem_nhds hy] with y' hy'
    exact d.R.mem _ _ (mem_atlas_target d pt hcov hy').2
  have hcomp : (weight d pt hcov A hA hsp.1).φ l ∘ ((atlas d pt hcov).chart l).symm =
      (fun z => 2 * Real.log (A.h z)) ∘
        (fun y p => d.R.lift (pt l) (((atlas d pt hcov).chart l).symm y) p) := rfl
  rw [hcomp, levi_comp w hG (contDiffAt_const.mul hlog), levi_const_mul 2 hlog]
  exact mul_nonneg (by norm_num) (hsp.2 _ hmem _ (isConeTangent_of_map hP0 hG hpts w))

def smoothVol : SmoothVolume (atlas d pt hcov) where
  μ := d.dV
  isProb := d.vol.1
  dens i := (d.vol.2 (chartIdx d.R.A (pt i))).choose
  smooth i := (d.vol.2 (chartIdx d.R.A (pt i))).choose_spec.1.mono fun _ hy => hy.1
  pos i y hy := (d.vol.2 (chartIdx d.R.A (pt i))).choose_spec.2.1 y hy.1
  chart_lintegral i g hg :=
    lintegral_chart (d.R.A.chart (chartIdx d.R.A (pt i))) d.dV _ (d.vol.2 _).choose_spec.1.continuousOn
      (d.vol.2 _).choose_spec.2.2 (d.R.isOpen_U (pt i)) g hg

def sec (b : MvPolynomial (Σ k, ι k) ℚ) : Fin (atlas d pt hcov).n → d.R.X → ℂ :=
  fun i => ((atlas d pt hcov).chart i).source.indicator
    fun x => eval (d.R.lift (pt i) x) (map (algebraMap ℚ ℂ) b)

theorem sec_apply_of_mem (b : MvPolynomial (Σ k, ι k) ℚ) {i : Fin r} {x : d.R.X}
    (hx : x ∈ ((atlas d pt hcov).chart i).source) :
    sec d pt hcov b i x = eval (d.R.lift (pt i) x) (map (algebraMap ℚ ℂ) b) :=
  indicator_of_mem hx _

theorem sec_mem {n : ℕ} {b : MvPolynomial (Σ k, ι k) ℚ} (hb : IsMultiHomog b (blockDeg d.k₀ n)) :
    sec d pt hcov b ∈ (bundle d pt hcov).sections n := by
  refine ⟨fun i l y hy => ?_, fun i k x hx => ?_, fun i x hx => indicator_of_notMem hx _⟩
  · have hS : IsOpen (((atlas d pt hcov).chart l).target ∩ ((atlas d pt hcov).chart l).symm ⁻¹'
        ((atlas d pt hcov).chart i).source) :=
      ((atlas d pt hcov).chart l).isOpen_inter_preimage_symm ((atlas d pt hcov).chart i).open_source
    have hG := analyticAt_lift d pt hcov i l hy.1 (mem_atlas_source d pt hcov hy.2)
    refine (AnalyticAt.aeval_mvPolynomial
      (f := fun y p => d.R.lift (pt i) (((atlas d pt hcov).chart l).symm y) p)
      (analyticAt_pi_iff.1 hG) (map (algebraMap ℚ ℂ) b)).congr ?_
    filter_upwards [hS.mem_nhds hy] with y' hy'
    have hm : ((atlas d pt hcov).chart l).symm y' ∈ ((atlas d pt hcov).chart i).source := hy'.2
    rw [Function.comp_apply, sec_apply_of_mem d pt hcov b hm]
    simp [aeval_def, eval]
  · obtain ⟨c, hc, hz⟩ := sameOrbit_lift d pt hcov hx.1 hx.2
    rw [sec_apply_of_mem d pt hcov b hx.1, sec_apply_of_mem d pt hcov b hx.2]
    show _ = blockRatio d.k₀ (d.R.lift (pt i) x) (d.R.lift (pt k) x) ^ n * _
    rw [hz, blockRatio_eq c ((lift_mem d pt hcov hx.2).1 d.k₀), eval_torus _ hb]

theorem lift_chartIdx (y : d.R.X) :
    ∃ c : K → ℂ, (∀ k, c k ≠ 0) ∧
      d.R.lift (pt (chartIdx (atlas d pt hcov) y)) y = fun p => c p.1 * blockPt d y p := by
  have hx : y ∈ ((atlas d pt hcov).chart (chartIdx (atlas d pt hcov) y)).source :=
    Classical.choose_spec ((atlas d pt hcov).cover y)
  exact d.R.compat _ _ y ⟨mem_atlas_source d pt hcov hx, d.R.mem_U y⟩

theorem locDens_eq_chernTopDens (A' : HermLine ι) (hA' : A'.a = unitDeg d.k₀) (hs : IsSmoothHerm A') (t : ℝ)
    (j : Fin r) {y : Fin D → ℂ} (hy : y ∈ ((atlas d pt hcov).chart j).target) :
    locDens (atlas d pt hcov) (fun _ => blockInterpPot d d.A A' t) j y =
      chernTopDens ((weight d pt hcov d.A d.deg d.semipos.1).lerp (weight d pt hcov A' hA' hs) t) j y := by
  obtain ⟨hy1, hyU⟩ := mem_atlas_target d pt hcov hy
  have hΦ : ∀ _ : Fin D, IsPotential d.R.A (blockInterpPot d d.A A' t) :=
    fun _ => isPotential_blockInterpPot d hs t
  have hbase := locDensBase d.R.A (fun _ => blockInterpPot d d.A A' t) hΦ (chartIdx d.R.A (pt j)) y hy1
    (fun _ => pt j) (fun _ => hyU)
  set ψ : (Fin D → ℂ) → ℝ := fun y' =>
    (1 - t) * Real.log (d.A.h (d.R.lift (pt j) (((atlas d pt hcov).chart j).symm y'))) +
      t * Real.log (A'.h (d.R.lift (pt j) (((atlas d pt hcov).chart j).symm y'))) with hψ
  have hL : locDens (atlas d pt hcov) (fun _ => blockInterpPot d d.A A' t) j y = maDens (fun _ => ψ) y :=
    hbase
  have hgerm : ((weight d pt hcov d.A d.deg d.semipos.1).lerp (weight d pt hcov A' hA' hs) t).φ j ∘
      ((atlas d pt hcov).chart j).symm =ᶠ[𝓝 y] fun y' => 2 * ψ y' := by
    refine Filter.Eventually.of_forall fun y' => ?_
    simp only [Function.comp_apply, Weight.lerp, weight, hψ]
    ring
  rw [hL]
  unfold chernTopDens maDens
  rw [hessCGerm _ _ y hgerm, hessC_const_mul', ReciprocityTheory.AnForm.A.mdisc_const, smul_smul, Matrix.det_smul,
    Fintype.card_fin]
  have hc : ((1 / Real.pi : ℝ) : ℂ) * ((2 : ℝ) : ℂ) = ((2 / Real.pi : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hc, ← Complex.ofReal_pow, Complex.re_ofReal_mul]
  ring

end Datum

end BlockResolutionMetricPair

open BlockResolutionMetricPair in

theorem BlockResolutionMetricPair.proof (h : BergmanDensChartSum.Statement) : BlockResolutionMetricPair.Statement := by
  intro D K _ _ ι _ Ω _ _ d A' P0' hA' hP0' hsp'
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (nbhd d) (isOpen_nbhd d)
    fun x _ => mem_iUnion.2 ⟨x, mem_nbhd d x⟩
  let pt : Fin t.card → d.R.X := fun i => (t.equivFin.symm i : d.R.X)
  have hcov : ∀ x, ∃ i, x ∈ nbhd d (pt i) := by
    intro x
    obtain ⟨x', hx', hx⟩ := mem_iUnion₂.1 (ht (mem_univ x))
    exact ⟨t.equivFin ⟨x', hx'⟩, by simpa [pt] using hx⟩
  refine ⟨atlas d pt hcov, bundle d pt hcov, weight d pt hcov d.A d.deg d.semipos.1,
    weight d pt hcov A' hA' hsp'.1, smoothVol d pt hcov, fun _ b => sec d pt hcov b, refine_compatible _ _ _ _ _,
    weight_isSemipositive d pt hcov d.A d.deg d.P0 d.normalForm_baseLattice_le_dualSpan_sup_line d.semipos,
    weight_isSemipositive d pt hcov A' hA' P0' hP0' hsp', rfl, fun n b hb => sec_mem d pt hcov hb,
    fun y => ?_, fun s _ g hg => ?_⟩
  · obtain ⟨c, hc, hz⟩ := lift_chartIdx d pt hcov y
    have hx : y ∈ ((atlas d pt hcov).chart (chartIdx (atlas d pt hcov) y)).source :=
      Classical.choose_spec ((atlas d pt hcov).cover y)
    refine ⟨c, hc, fun n b _ => ?_, ?_, ?_⟩
    · show sec d pt hcov b (chartIdx (atlas d pt hcov) y) y = _
      rw [sec_apply_of_mem d pt hcov b hx, hz]
    · show 2 * Real.log (d.A.h (d.R.lift (pt _) y)) = _
      rw [hz]
    · show 2 * Real.log (A'.h (d.R.lift (pt _) y)) = _
      rw [hz]
  · have hΦ : ∀ _ : Fin D, IsPotential d.R.A (blockInterpPot d d.A A' s) :=
      fun _ => isPotential_blockInterpPot d hsp'.1 s
    have hMI := mIntegrableCont d.R.A _ hΦ g hg
    have hcomp := refine_compatible d.R.A (fun i => chartIdx d.R.A (pt i)) (fun i => d.R.U (pt i))
      (fun i => d.R.isOpen_U (pt i)) fun x => (hcov x).imp fun _ hx => ⟨hx.2, hx.1⟩
    rw [(mIntAtlasIndep d.R.A (atlas d pt hcov) ⟨hcomp.2, hcomp.1⟩ _ hΦ g hMI).2]
    have hP : Nonempty (ChartPartition (atlas d pt hcov)) := existsPartition _
    rw [h (atlas d pt hcov) (bundle d pt hcov) _ (smoothVol d pt hcov) hP.some g hg]
    unfold mInt
    rw [dif_pos hP]
    unfold integralWith
    congr 1
    refine Finset.sum_congr rfl fun j _ => setIntegral_congr_fun
      (((atlas d pt hcov).chart j).open_target.measurableSet) fun y hy => ?_
    simp only
    rw [locDens_eq_chernTopDens d pt hcov A' hA' hsp'.1 s j hy]

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
