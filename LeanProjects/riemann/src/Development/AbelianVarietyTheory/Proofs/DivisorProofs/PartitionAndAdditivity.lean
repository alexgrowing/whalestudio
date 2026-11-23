import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LineSCShortExact
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GluedChartDensityMeasureAddOfCompatibleOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopDegreeDensityPullbackEqNormSqDetMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlueMeasUnivNeTopOfCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFormMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteSmoothPartitionUnityHolAtlas
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernPartOverProperClosedEqZero

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ENNReal ContDiff
open GlobalTheory.CxForm GlobalTheory.ChartGlue GlobalTheory.LineForm

namespace GlobalTheory.FormPartition

variable {M : Type} [TopologicalSpace M] {n : ℕ} (A : HolAtlas M n)

theorem exists_bump [T2Space M] (x : M) {U : Set M} (hU : IsOpen U) (hx : x ∈ U) :
    ∃ (i : A.ι) (ψ : M → ℝ), A.SmoothOn univ (fun y => (ψ y : ℂ)) ∧ (∀ y, 0 ≤ ψ y ∧ ψ y ≤ 1) ∧
      tsupport ψ ⊆ U ∩ (A.e i).source ∧ ∀ᶠ y in 𝓝 x, ψ y = 1 := by
  classical
  obtain ⟨i, hxe⟩ := A.cover x
  set e := A.e i with he
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp (isOpen_over e hU) (e x) (mem_over e hxe hx)
  let β : ContDiffBump (e x) := ⟨ε / 4, ε / 2, by linarith, by linarith⟩
  have hcb : Metric.closedBall (e x) (ε / 2) ⊆ e.target ∩ e.symm ⁻¹' U :=
    (Metric.closedBall_subset_ball (half_lt_self hε)).trans hball
  set C := e.symm '' Metric.closedBall (e x) (ε / 2) with hC
  have hCc : IsCompact C := (isCompact_closedBall (e x) (ε / 2)).image_of_continuousOn
    (e.continuousOn_symm.mono fun y hy => (hcb hy).1)
  have hCsub : C ⊆ U ∩ e.source := by
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨(hcb hy).2, e.map_target (hcb hy).1⟩
  let ψ : M → ℝ := fun w => if w ∈ e.source then β (e w) else 0
  have hsupp : Function.support ψ ⊆ C := by
    intro w hw
    simp only [Function.mem_support, ψ] at hw
    split_ifs at hw with hws
    · have : e w ∈ Metric.ball (e x) (ε / 2) := by
        rw [← β.support_eq]; exact hw
      exact ⟨e w, Metric.ball_subset_closedBall this, e.left_inv hws⟩
    · exact absurd rfl hw
  have hts : tsupport ψ ⊆ C := closure_minimal hsupp hCc.isClosed
  refine ⟨i, ψ, ?_, fun y => ?_, hts.trans hCsub, ?_⟩
  · intro k
    rw [preimage_univ, inter_univ]
    apply contDiffOn_of_locally_contDiffOn
    intro y hy
    by_cases hys : (A.e k).symm y ∈ e.source
    · refine ⟨(A.e k).target ∩ (A.e k).symm ⁻¹' e.source,
        (A.e k).isOpen_inter_preimage_symm e.open_source, ⟨hy, hys⟩, ?_⟩
      have hβ : ContDiff ℝ ∞ (fun y : V n => ((β y : ℝ) : ℂ)) :=
        Complex.ofRealCLM.contDiff.comp β.contDiff
      refine ((hβ.comp_contDiffOn (A.contDiffOn_real_transition k i)).mono inter_subset_right).congr
        fun v hv => ?_
      have hv1 : (A.e k).symm v ∈ e.source := hv.2.2
      simp only [Function.comp, ψ, if_pos hv1]
      rfl
    · refine ⟨(A.e k).target ∩ (A.e k).symm ⁻¹' Cᶜ,
        (A.e k).isOpen_inter_preimage_symm hCc.isClosed.isOpen_compl,
        ⟨hy, fun h => hys (hCsub h).2⟩, ?_⟩
      refine (contDiffOn_const (c := (0 : ℂ))).congr fun v hv => ?_
      have : ψ ((A.e k).symm v) = 0 := by
        by_contra h
        exact hv.2.2 (hsupp h)
      simp [Function.comp, this]
  · simp only [ψ]
    split_ifs
    exacts [⟨β.nonneg, β.le_one⟩, ⟨le_rfl, zero_le_one⟩]
  · have ho : IsOpen (e.source ∩ e ⁻¹' Metric.ball (e x) (ε / 4)) :=
      e.isOpen_inter_preimage Metric.isOpen_ball
    filter_upwards [ho.mem_nhds ⟨hxe, Metric.mem_ball_self (by linarith)⟩] with w hw
    simp only [ψ, if_pos hw.1]
    exact β.one_of_mem_closedBall (Metric.ball_subset_closedBall hw.2)

theorem exists_partition [CompactSpace M] [T2Space M] {κ : Type*} (U : κ → Set M) (hU : ∀ a, IsOpen (U a))
    (hc : ∀ y, ∃ a, y ∈ U a) :
    ∃ (N : ℕ) (a : Fin N → κ) (c : Fin N → A.ι) (χ : Fin N → M → ℝ), (∀ j, A.SmoothOn univ fun y => (χ j y : ℂ)) ∧
      (∀ j y, 0 ≤ χ j y) ∧ (∀ y, ∑ j, χ j y = 1) ∧
      ∀ j, IsCompact (tsupport (χ j)) ∧ tsupport (χ j) ⊆ U (a j) ∧ tsupport (χ j) ⊆ (A.e (c j)).source := by
  classical
  choose a ha using hc
  choose E Ψ hΨs hΨ0 hΨt hΨ1 using fun x => exists_bump A x (hU (a x)) (ha x)
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x : M => interior {y | Ψ x y = 1})
    (fun _ => isOpen_interior) (fun y _ => mem_iUnion.2 ⟨y, mem_interior_iff_mem_nhds.2 (hΨ1 y)⟩)
  let p : Fin t.card → M := fun i => (t.equivFin.symm i : M)
  let ψ : Fin t.card → M → ℝ := fun i => Ψ (p i)
  have hsum : ∀ x, ∑ i, ψ i x * ∏ j ∈ Finset.univ with j < i, (1 - ψ j x) =
      1 - ∏ i, (1 - ψ i x) := fun x => by
    rw [Finset.prod_one_sub_ordered]; ring
  refine ⟨t.card, fun i => a (p i), fun i => E (p i), fun i x => ψ i x * ∏ j ∈ Finset.univ with j < i, (1 - ψ j x),
    fun i k => ?_, fun i x => ?_, fun x => ?_, fun i => ⟨(isClosed_tsupport _).isCompact,
      (tsupport_mul_subset_left.trans (hΨt (p i))).trans inter_subset_left,
      (tsupport_mul_subset_left.trans (hΨt (p i))).trans inter_subset_right⟩⟩
  · refine ((hΨs (p i) k).mul (contDiffOn_prod (t := Finset.univ.filter (· < i))
      fun j _ => (contDiffOn_const (c := (1 : ℂ))).sub (hΨs (p j) k))).congr fun v _ => ?_
    simp [Function.comp, ψ]
  · exact mul_nonneg (hΨ0 _ _).1 (Finset.prod_nonneg fun j _ => sub_nonneg.2 (hΨ0 _ _).2)
  · rw [hsum]
    obtain ⟨u, hu, hxu⟩ := mem_iUnion₂.1 (ht (mem_univ x))
    have h1 : ψ (t.equivFin ⟨u, hu⟩) x = 1 := by
      have : p (t.equivFin ⟨u, hu⟩) = u := by simp [p]
      simp only [ψ, this]
      exact (interior_subset hxu : x ∈ {y | Ψ u y = 1})
    rw [Finset.prod_eq_zero (Finset.mem_univ (t.equivFin ⟨u, hu⟩)) (by rw [h1]; ring)]
    ring

theorem loc_sum {κ : Type*} (s : Finset κ) (α : κ → A.Fld) (i : A.ι) (v : V n) :
    A.loc (∑ j ∈ s, α j) i v = ∑ j ∈ s, A.loc (α j) i v := by
  unfold HolAtlas.loc
  split_ifs
  · exact Finset.sum_apply _ _ _
  · exact Finset.sum_const_zero.symm

theorem isForm_sum {κ : Type*} (s : Finset κ) {α : κ → A.Fld} (h : ∀ j ∈ s, A.IsForm (α j)) :
    A.IsForm (∑ j ∈ s, α j) := by
  refine ⟨fun i S => ?_, fun x x' e => ?_⟩
  · simp only [loc_sum, map_sum, Finsupp.finsetSum_apply]
    exact ContDiffOn.sum fun j hj => (h j hj).smooth i S
  · rw [Finset.sum_apply, Finset.sum_apply, map_sum]
    exact Finset.sum_congr rfl fun j hj => (h j hj).compat x x' e

theorem isForm_fn_mul {χ : M → ℝ} (hχ : A.SmoothOn univ fun y => (χ y : ℂ)) {α : A.Fld} (hα : A.IsForm α) :
    A.IsForm (A.fn χ * α) :=
  FormMul.isForm_mul A _ _ (A.isForm_fn hχ) hα

theorem sum_fn_mul {κ : Type*} (s : Finset κ) {χ : κ → M → ℝ} (h : ∀ y, ∑ j ∈ s, χ j y = 1) (α : A.Fld) :
    ∑ j ∈ s, A.fn (χ j) * α = α := by
  funext x
  rw [Finset.sum_apply]
  simp only [Pi.mul_apply, HolAtlas.fn]
  rw [← Finset.sum_mul, ← map_sum, ← Complex.ofReal_sum, h, Complex.ofReal_one, map_one, one_mul]

def rd (α : A.Fld) (i : A.ι) (v : V n) : ℝ := (dens (A.loc α i v)).re

theorem rd_add (α β : A.Fld) (i : A.ι) (v : V n) : rd A (α + β) i v = rd A α i v + rd A β i v := by
  have : A.loc (α + β) i v = A.loc α i v + A.loc β i v := by
    unfold HolAtlas.loc; split_ifs
    · rfl
    · exact (add_zero 0).symm
  simp only [rd, this, dens, map_add, Finsupp.add_apply, add_div, Complex.add_re]

theorem rd_zero (i : A.ι) (v : V n) : rd A 0 i v = 0 := by
  have : A.loc 0 i v = 0 := by
    unfold HolAtlas.loc; split_ifs <;> rfl
  simp [rd, this, dens]

def Good (r : A.ι → V n → ℝ) : Prop :=
  (∀ i, ContinuousOn (r i) (A.e i).target) ∧
  ∀ i j y, y ∈ (A.e i).source → y ∈ (A.e j).source →
    r i (A.e i y) = ‖transDet (A.e i) (A.e j) y‖ ^ 2 * r j (A.e j y)

theorem good_rd {α : A.Fld} (hα : A.IsForm α) : Good A (rd A α) := by
  refine ⟨fun i => Complex.continuous_re.comp_continuousOn ((hα.smooth i Finset.univ).continuousOn.div_const _),
    fun i j y hi hj => ?_⟩
  have h1 := A.loc_crd α (⟨(i, y), hi⟩ : A.Pt)
  have h2 := A.loc_crd α (⟨(j, y), hj⟩ : A.Pt)
  have h3 := hα.compat (⟨(i, y), hi⟩ : A.Pt) ⟨(j, y), hj⟩ rfl
  simp only [rd]
  erw [h1, h2, h3, dens_pull]
  rw [Complex.re_ofReal_mul]
  rfl

theorem good_sign {α : A.Fld} (hα : A.IsForm α) (ε : ℤˣ) : Good A fun i v => ((ε : ℤ) : ℝ) * rd A α i v :=
  ⟨fun i => continuousOn_const.mul ((good_rd A hα).1 i),
    fun i j y hi hj => by simp only [(good_rd A hα).2 i j y hi hj]; ring⟩

variable {A} in
theorem Good.compat {r : A.ι → V n → ℝ} (h : Good A r) (i j : A.ι) (y : M) (hi : y ∈ (A.e i).source)
    (hj : y ∈ (A.e j).source) : ENNReal.ofReal (r i (A.e i y)) =
      ENNReal.ofReal (‖transDet (A.e i) (A.e j) y‖ ^ 2) * ENNReal.ofReal (r j (A.e j y)) := by
  rw [h.2 i j y hi hj, ENNReal.ofReal_mul (by positivity)]

variable {A} in
theorem Good.aem {r : A.ι → V n → ℝ} (hr : Good A r) (i : A.ι) :
    AEMeasurable (fun v => ENNReal.ofReal (r i (A.e i ((A.e i).symm v)))) (volume.restrict (A.e i).target) := by
  have h := (ENNReal.continuous_ofReal.comp_continuousOn (hr.1 i)).aemeasurable (μ := volume)
    (A.e i).open_target.measurableSet
  refine h.congr ((ae_restrict_iff' (A.e i).open_target.measurableSet).2 (Eventually.of_forall fun v hv => ?_))
  simp [(A.e i).right_inv hv]

theorem ofReal_posNeg (x y : ℝ) :
    ENNReal.ofReal (x + y) + ENNReal.ofReal (-x) + ENNReal.ofReal (-y) =
      ENNReal.ofReal (-(x + y)) + ENNReal.ofReal x + ENNReal.ofReal y := by
  have m : ∀ t : ℝ, ENNReal.ofReal t = ENNReal.ofReal (max t 0) := fun t => by
    rcases le_total t 0 with h | h
    · simp [h, ENNReal.ofReal_of_nonpos h]
    · simp [h]
  have k : max (x + y) 0 + max (-x) 0 + max (-y) 0 = max (-(x + y)) 0 + max x 0 + max y 0 := by
    simp only [max_def]; split_ifs <;> linarith
  rw [m (x + y), m (-x), m (-y), m (-(x + y)), m x, m y,
    ← ENNReal.ofReal_add (le_max_right _ _) (le_max_right _ _),
    ← ENNReal.ofReal_add (by positivity) (le_max_right _ _),
    ← ENNReal.ofReal_add (le_max_right _ _) (le_max_right _ _),
    ← ENNReal.ofReal_add (by positivity) (le_max_right _ _), k]

variable [MeasurableSpace M] [BorelSpace M]

theorem part_eq (α : A.Fld) (ε : ℤˣ) :
    A.part α ε = glueMeas A.e fun i y => ENNReal.ofReal (((ε : ℤ) : ℝ) * rd A α i (A.e i y)) := rfl

theorem part_zero (ε : ℤˣ) : A.part 0 ε = 0 := by
  rw [part_eq]
  refine le_antisymm (iSup_le fun i => Measure.le_iff.2 fun S hS => ?_) bot_le
  rw [chartMeas_apply _ _ hS]
  simp [rd_zero]

variable [SecondCountableTopology M]

theorem part_apply {α : A.Fld} (hα : A.IsForm α) (ε : ℤˣ) (i : A.ι) {S : Set M} (hS : MeasurableSet S)
    (h : S ⊆ (A.e i).source) :
    A.part α ε S = ∫⁻ v in A.e i '' S, ENNReal.ofReal (((ε : ℤ) : ℝ) * rd A α i (A.e i ((A.e i).symm v))) := by
  rw [part_eq, glueMeas_apply _ _ A.holo (good_sign A hα ε).compat i hS h, chartMeas_apply_of_subset _ _ hS h]

theorem aem_part {α : A.Fld} (hα : A.IsForm α) (ε : ℤˣ) (i : A.ι) {S : Set M} (h : S ⊆ (A.e i).source) :
    AEMeasurable (fun v => ENNReal.ofReal (((ε : ℤ) : ℝ) * rd A α i (A.e i ((A.e i).symm v))))
      (volume.restrict (A.e i '' S)) :=
  ((good_sign A hα ε).aem i).mono_measure (Measure.restrict_mono
    (by rintro _ ⟨y, hy, rfl⟩; exact (A.e i).map_source (h hy)) le_rfl)

theorem isForm_add {α β : A.Fld} (hα : A.IsForm α) (hβ : A.IsForm β) : A.IsForm (α + β) := by
  have := isForm_sum A Finset.univ (α := fun b : Bool => cond b α β) fun j _ => by cases j; exacts [hβ, hα]
  rwa [Fintype.sum_bool] at this

theorem isFiniteMeasure_part [CompactSpace M] {α : A.Fld} (hα : A.IsForm α) (ε : ℤˣ) :
    IsFiniteMeasure (A.part α ε) :=
  ⟨by
    rw [part_eq]
    exact lt_top_iff_ne_top.2 (glueMeas_univ_ne_top_of_compact A.e A.cover A.holo
      (fun i v => ((ε : ℤ) : ℝ) * rd A α i v) (good_sign A hα ε).1 (good_sign A hα ε).2)⟩

theorem part_balance {α β : A.Fld} (hα : A.IsForm α) (hβ : A.IsForm β) (ε : ℤˣ) :
    A.part (α + β) ε + A.part α (-ε) + A.part β (-ε) = A.part (α + β) (-ε) + A.part α ε + A.part β ε := by
  have hs := isForm_add A hα hβ
  refine ext_of_cover (fun i => (A.e i).source) (fun i => (A.e i).open_source) A.cover fun i S hS h => ?_
  simp only [Measure.add_apply, part_apply A hα _ i hS h, part_apply A hβ _ i hS h, part_apply A hs _ i hS h]
  rw [← lintegral_add_left' (aem_part A hs _ i h), ← lintegral_add_left' (aem_part A hs _ i h),
    ← lintegral_add_right' _ (aem_part A hβ _ i h), ← lintegral_add_right' _ (aem_part A hβ _ i h)]
  refine lintegral_congr fun v => ?_
  simp only [rd_add, Units.val_neg, Int.cast_neg, neg_mul, mul_add]
  rw [← neg_add]
  exact ofReal_posNeg _ _

theorem part_add_le {α β : A.Fld} (ε : ℤˣ) (hα : A.IsForm α) (hβ : A.IsForm β) :
    A.part (α + β) ε ≤ A.part α ε + A.part β ε := by
  have key : glueMeas A.e (fun i y => ENNReal.ofReal (((ε : ℤ) : ℝ) * rd A α i (A.e i y)) +
      ENNReal.ofReal (((ε : ℤ) : ℝ) * rd A β i (A.e i y))) = A.part α ε + A.part β ε := by
    ext S hS
    exact glueMeas_add_of_compat_on A.e A.holo A.cover hS _ _
      (fun i j y _ hi hj => (good_sign A hα ε).compat i j y hi hj)
      (fun i j y _ hi hj => (good_sign A hβ ε).compat i j y hi hj)
      fun i => ((good_sign A hα ε).aem i).mono_measure (Measure.restrict_mono inter_subset_left le_rfl)
  rw [← key, part_eq]
  exact iSup_mono fun i => Measure.le_iff.2 fun S hS => by
    rw [chartMeas_apply _ _ hS, chartMeas_apply _ _ hS]
    exact lintegral_mono fun v => by beta_reduce; rw [rd_add, mul_add]; exact ENNReal.ofReal_add_le

theorem wInt_add {g : M → ℝ} {α β : A.Fld} (hα : A.IsForm α) (hβ : A.IsForm β)
    (ga : ∀ ε : ℤˣ, Integrable g (A.part α ε)) (gb : ∀ ε : ℤˣ, Integrable g (A.part β ε)) :
    (∀ ε : ℤˣ, Integrable g (A.part (α + β) ε)) ∧ wInt A g (α + β) = wInt A g α + wInt A g β := by
  have gs : ∀ ε : ℤˣ, Integrable g (A.part (α + β) ε) := fun ε =>
    ((ga ε).add_measure (gb ε)).mono_measure (part_add_le A ε hα hβ)
  refine ⟨gs, ?_⟩
  have key := congrArg (fun μ : Measure M => ∫ y, g y ∂μ) (part_balance A hα hβ 1)
  beta_reduce at key
  rw [integral_add_measure (((gs 1).add_measure (ga (-1)))) (gb (-1)),
    integral_add_measure (gs 1) (ga (-1)),
    integral_add_measure (((gs (-1)).add_measure (ga 1))) (gb 1),
    integral_add_measure (gs (-1)) (ga 1)] at key
  simp only [wInt]
  linarith

theorem wInt_sum {κ : Type*} (s : Finset κ) {g : M → ℝ} {α : κ → A.Fld} (hα : ∀ j ∈ s, A.IsForm (α j))
    (hg : ∀ j ∈ s, ∀ ε : ℤˣ, Integrable g (A.part (α j) ε)) :
    (∀ ε : ℤˣ, Integrable g (A.part (∑ j ∈ s, α j) ε)) ∧ wInt A g (∑ j ∈ s, α j) = ∑ j ∈ s, wInt A g (α j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [wInt, part_zero]
  | insert a s ha ih =>
    have h' : ∀ j ∈ s, A.IsForm (α j) := fun j hj => hα j (Finset.mem_insert_of_mem hj)
    obtain ⟨i₁, i₂⟩ := ih h' fun j hj => hg j (Finset.mem_insert_of_mem hj)
    obtain ⟨k₁, k₂⟩ := wInt_add A (hα a (Finset.mem_insert_self a s)) (isForm_sum A s h')
      (hg a (Finset.mem_insert_self a s)) i₁
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact ⟨k₁, by rw [k₂, i₂]⟩

theorem integral_sum [CompactSpace M] {κ : Type*} (s : Finset κ) {α : κ → A.Fld} (hα : ∀ j ∈ s, A.IsForm (α j)) :
    A.integral (∑ j ∈ s, α j) = ∑ j ∈ s, A.integral (α j) := by
  simp only [← wInt_one]
  exact (wInt_sum A s hα fun j hj ε => by
    have := isFiniteMeasure_part A (hα j hj) ε
    exact integrable_const _).2

section Variety

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {D : ℕ} (h : IsRegVar p D) (σ : k →+* ℂ)

theorem exists_partition_regVar {κ : Type*} (U : κ → Set (CxPts p σ)) (hU : ∀ a, IsOpen (U a))
    (hc : ∀ y, ∃ a, y ∈ U a) :
    ∃ (N : ℕ) (a : Fin N → κ) (c : Fin N → (h.atlas σ).ι) (χ : Fin N → CxPts p σ → ℝ),
      (∀ j, (h.atlas σ).SmoothOn univ fun y => (χ j y : ℂ)) ∧ (∀ j y, 0 ≤ χ j y) ∧ (∀ y, ∑ j, χ j y = 1) ∧
      ∀ j, IsCompact (tsupport (χ j)) ∧ tsupport (χ j) ⊆ U (a j) ∧
        tsupport (χ j) ⊆ ((h.atlas σ).e (c j)).source :=
  have := h.toIsArithVar.compactSpace σ
  have := CxPts.t2Space_cxPts_of_isProjOver σ h.isProjOver
  exists_partition _ U hU hc

theorem integral_sum_regVar {κ : Type*} (s : Finset κ) {α : κ → (h.atlas σ).Fld}
    (hα : ∀ j ∈ s, (h.atlas σ).IsForm (α j)) :
    (h.atlas σ).integral (∑ j ∈ s, α j) = ∑ j ∈ s, (h.atlas σ).integral (α j) :=
  have := h.toIsArithVar.compactSpace σ
  have := CxPts.secondCountableTopology_of_isProjOver σ h.isProjOver
  integral_sum _ s hα

end Variety

end GlobalTheory.FormPartition
