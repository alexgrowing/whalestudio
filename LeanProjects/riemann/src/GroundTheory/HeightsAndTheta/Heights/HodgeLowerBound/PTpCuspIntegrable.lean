import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsTpCuspIntegrable
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsModelLogIntegrable
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsBoundaryNull
import GroundTheory.HeightsAndTheta.Heights.Regularisation.GlueCharts
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo Filter Topology
open ReciprocityTheory.AnForm.M (FinHolAtlas)

namespace CuspWeightIntegrable

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

omit [∀ k, Fintype (ι k)] in

theorem isOpen_blocks : IsOpen {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
  simp only [Set.ofPred_forall, Set.ofPred_exists]
  exact isOpen_iInter_of_finite fun k => isOpen_iUnion fun i =>
    isOpen_ne_fun (continuous_apply _) continuous_const

def logRatio (A A' : HermLine ι) (z : (Σ k, ι k) → ℂ) : ℝ := Real.log (A.h z) - Real.log (A'.h z)

theorem continuousAt_logRatio {A A' : HermLine ι} (hA : IsSmoothHerm A) (hA' : IsSmoothHerm A')
    {z : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) : ContinuousAt (logRatio A A') z := by
  have hn := isOpen_blocks.mem_nhds hz
  exact ((hA.continuousOn.continuousAt hn).log (A.pos z hz).ne').sub
    ((hA'.continuousOn.continuousAt hn).log (A'.pos z hz).ne')

omit [∀ k, Fintype (ι k)] in

theorem logRatio_torusSmul {A A' : HermLine ι} (ha : A.a = A'.a) (c : K → ℂ) (hc : ∀ k, c k ≠ 0)
    {z : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    logRatio A A' (torusSmul c z) = logRatio A A' z := by
  have hpos : 0 < ∏ k, ‖c k‖ ^ A.a k := Finset.prod_pos fun k _ => zpow_pos (norm_pos_iff.2 (hc k)) _
  have e : torusSmul c z = fun x => c x.1 * z x := rfl
  have h1 := A.smul c z hc
  have h2 := A'.smul c z hc
  rw [← ha] at h2
  unfold logRatio
  rw [e, h1, h2, Real.log_mul hpos.ne' (A.pos z hz).ne', Real.log_mul hpos.ne' (A'.pos z hz).ne']
  ring

variable {P : Ideal (MRing ι)} {d : ℕ}

def descend (M : CxModel P d) (v : ((Σ k, ι k) → ℂ) → ℝ) (x : M.Xc) : ℝ := v (M.surj x).choose

omit [Fintype K] [∀ k, Fintype (ι k)] in

theorem descend_proj (M : CxModel P d) {v : ((Σ k, ι k) → ℂ) → ℝ}
    (hv : ∀ c : K → ℂ, (∀ k, c k ≠ 0) → ∀ z ∈ mcPts P, v (torusSmul c z) = v z)
    {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts P) : descend M v (M.proj z) = v z := by
  obtain ⟨hz', hpz⟩ := (M.surj (M.proj z)).choose_spec
  obtain ⟨c, hc, hzc⟩ := (M.fibre _ hz' z hz).1 hpz
  have h := hv c hc _ hz'
  rw [← hzc] at h
  exact h.symm

theorem continuousAt_of_holoOn {X : Type} [TopologicalSpace X] {A : FinHolAtlas d X} {U : Set X}
    {f : X → ℂ} (hf : A.HoloOn U f) {x : X} (hx : x ∈ U) : ContinuousAt f x := by
  obtain ⟨j, hj⟩ := A.cover x
  have h1 : ContinuousAt (f ∘ (A.chart j).symm) (A.chart j x) :=
    (hf j _ ⟨(A.chart j).map_source hj, by simpa [(A.chart j).left_inv hj] using hx⟩).continuousAt
  have h2 : ContinuousAt ((f ∘ (A.chart j).symm) ∘ A.chart j) x := h1.comp ((A.chart j).continuousAt hj)
  refine h2.congr ?_
  filter_upwards [(A.chart j).open_source.mem_nhds hj] with y hy
  simp [(A.chart j).left_inv hy]

theorem continuous_descend (M : CxModel P d) {A A' : HermLine ι} (hA : IsSmoothHerm A)
    (hA' : IsSmoothHerm A') (ha : A.a = A'.a) : Continuous (descend M (logRatio A A')) := by
  have hv : ∀ c : K → ℂ, (∀ k, c k ≠ 0) → ∀ z ∈ mcPts P,
      logRatio A A' (torusSmul c z) = logRatio A A' z := fun c hc z hz => logRatio_torusSmul ha c hc hz.1
  refine continuous_iff_continuousAt.2 fun x => ?_
  obtain ⟨U, hU, hxU, s, hs, hholo⟩ := M.sections x
  have hsc : ContinuousAt s x := continuousAt_pi.2 fun p => continuousAt_of_holoOn (hholo p) hxU
  have h : ContinuousAt (logRatio A A' ∘ s) x := (continuousAt_logRatio hA hA' (hs x hxU).1.1).comp hsc
  refine h.congr ?_
  filter_upwards [hU.mem_nhds hxU] with y hy
  have h' := descend_proj M hv (hs y hy).1
  rw [(hs y hy).2] at h'
  exact h'.symm

theorem upperSemicontinuous_ph {X : Type} [TopologicalSpace X] {A : FinHolAtlas d X}
    (B : GroundTheory.Heights₂.Heights.Regular.BoundedPshData A) : UpperSemicontinuous B.ph := by
  intro x
  obtain ⟨j, hj⟩ := B.cover x
  have hxs : x ∈ (B.chart j).source := B.mid_subset_source j (B.inner_subset_mid j hj)
  have hy : B.chart j x ∈ (B.chart j).target := (B.chart j).map_source hxs
  have hn := (B.chart j).open_target.mem_nhds hy
  have h1 : UpperSemicontinuousAt (fun y => B.q j y + B.ph ((B.chart j).symm y)) (B.chart j x) :=
    fun c hc => by
      have h := ((B.u_psh j).1 _ hy) c hc
      rwa [nhdsWithin_eq_nhds.2 hn] at h
  have h2 : UpperSemicontinuousAt (fun y => -B.q j y) (B.chart j x) :=
    ((B.q_smooth j).continuousOn.continuousAt hn).neg.upperSemicontinuousAt
  have h3 : UpperSemicontinuousAt (fun y => B.ph ((B.chart j).symm y)) (B.chart j x) := by
    have h := h1.add h2
    have e : (fun y => B.q j y + B.ph ((B.chart j).symm y) + -B.q j y) =
        fun y => B.ph ((B.chart j).symm y) := by
      funext y
      ring
    rwa [e] at h
  intro c hc
  have hc' : B.ph ((B.chart j).symm (B.chart j x)) < c := by rwa [(B.chart j).left_inv hxs]
  filter_upwards [((B.chart j).continuousAt hxs).eventually (h3 c hc'),
    (B.chart j).open_source.mem_nhds hxs] with y hy hys
  rwa [(B.chart j).left_inv hys] at hy

theorem continuousOn_ph {X : Type} [TopologicalSpace X] {A : FinHolAtlas d X}
    (R : GroundTheory.Heights₂.Heights.Regular.RegChartData A) : ContinuousOn R.ph R.Yo := by
  intro x hx
  obtain ⟨j, hj⟩ := R.cover x
  have hxs : x ∈ (R.chart j).source := R.mid_subset_source j (R.inner_subset_mid j hj)
  have h1 := (GroundTheory.Heights₂.Heights.Regular.contDiffAt_comp_symm_of_smoothOn (R.compat j) R.isOpen_Yo
    R.ph_smooth hx hxs).continuousAt
  have h2 : ContinuousAt ((R.ph ∘ (R.chart j).symm) ∘ R.chart j) x := h1.comp ((R.chart j).continuousAt hxs)
  refine (h2.congr ?_).continuousWithinAt
  filter_upwards [(R.chart j).open_source.mem_nhds hxs] with y hy
  simp [(R.chart j).left_inv hy]

variable {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] {Ω : Type} [Field Ω] [Algebra ℚ Ω]
  {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)]
  {D : ComponentData II Ψ K ι Ω E} {O Lt : Type} [CommRing O] [AddCommGroup Lt] [Module O Lt]

open Classical in

def uFn (X : ComponentSetting D O Lt) (x : X.M.Xc) : ℝ :=
  X.S'.B.ph x + descend X.M (logRatio X.S'.ref X.S.ref) x - X.S.R.Yo.piecewise X.S.R.ph (fun _ => 0) x

theorem ref_deg_eq (X : ComponentSetting D O Lt) : X.S'.ref.a = X.S.ref.a :=
  X.S'.ref_deg.trans X.S.ref_deg.symm

open Classical in

theorem measurable_uFn (X : ComponentSetting D O Lt) : @Measurable X.M.Xc ℝ (borel X.M.Xc) _ (uFn X) := by
  let _ : MeasurableSpace X.M.Xc := borel X.M.Xc
  have _ : BorelSpace X.M.Xc := ⟨rfl⟩
  refine ((upperSemicontinuous_ph X.S'.B).measurable.add
    (continuous_descend X.M X.S'.ref_smooth X.S.ref_smooth (ref_deg_eq X)).measurable).sub ?_
  exact ContinuousOn.measurable_piecewise (continuousOn_ph X.S.R) continuousOn_const
    X.S.R.isOpen_Yo.measurableSet

open Classical in

theorem uFn_bound (X : ComponentSetting D O Lt) :
    ∃ C C' : ℝ, ∀ x ∈ X.S.R.Yo, |uFn X x| ≤ C + C' * Real.log (X.S.R.r x) := by
  obtain ⟨CB, hCB⟩ := X.S'.B.bdd
  obtain ⟨CV, hCV⟩ := isCompact_univ.exists_bound_of_continuousOn
    (continuous_descend X.M X.S'.ref_smooth X.S.ref_smooth (ref_deg_eq X)).continuousOn
  refine ⟨CB + CV + |X.S.R.Cph|, |X.S.R.Clog|, fun x hx => ?_⟩
  have h1 := hCB x
  have h2 : |descend X.M (logRatio X.S'.ref X.S.ref) x| ≤ CV := by
    simpa [Real.norm_eq_abs] using hCV x (Set.mem_univ x)
  have hr : 0 ≤ Real.log (X.S.R.r x) := Real.log_nonneg (X.S.R.one_le_r x hx)
  have h3 := X.S.R.ph_le x hx
  have h4 : -(X.S.R.Clog * Real.log (X.S.R.r x)) ≤ X.S.R.ph x := by
    rw [← neg_mul]
    exact X.S.R.ph_ge x hx
  have h5 : X.S.R.Clog * Real.log (X.S.R.r x) ≤ |X.S.R.Clog| * Real.log (X.S.R.r x) :=
    mul_le_mul_of_nonneg_right (le_abs_self _) hr
  have h6 : 0 ≤ |X.S.R.Clog| * Real.log (X.S.R.r x) := mul_nonneg (abs_nonneg _) hr
  have h7 := le_abs_self X.S.R.Cph
  have h8 := abs_nonneg X.S.R.Cph
  have hu : uFn X x = X.S'.B.ph x + descend X.M (logRatio X.S'.ref X.S.ref) x - X.S.R.ph x := by
    simp [uFn, Set.piecewise_eq_of_mem _ _ _ hx]
  rw [hu]
  rw [abs_le] at h1 h2 ⊢
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

open Classical in

theorem cuspWeight_eq (X : ComponentSetting D O Lt) {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal D.y))
    (hzb : z ∉ D.Bd) (hY : X.M.proj z ∈ X.S.R.Yo) : X.Cd.cuspWeight z / 2 = uFn X (X.M.proj z) := by
  have hXo : z ∈ D.Xo ∩ mcPts (mCoordIdeal D.y) := ⟨⟨hz, hzb⟩, hz⟩
  have h1 := X.S'.ph_eq z hXo
  have h2 := X.S.ph_eq z hXo hY
  have h3 := descend_proj X.M (fun c hc z hz => logRatio_torusSmul (ref_deg_eq X) c hc hz.1) hz
  have hu : uFn X (X.M.proj z) = X.S'.B.ph (X.M.proj z) +
      descend X.M (logRatio X.S'.ref X.S.ref) (X.M.proj z) - X.S.R.ph (X.M.proj z) := by
    simp [uFn, Set.piecewise_eq_of_mem _ _ _ hY]
  rw [hu, h1, h2, h3]
  simp only [cuspCorr, logRatio, phMu]
  ring

end CuspWeightIntegrable

theorem TpCuspIntegrable.proof (hM : ModelLogIntegrable.Statement) (hBd : BoundaryNull.Statement) :
    TpCuspIntegrable.Statement := by
  intro II Ψ _ _ K _ ι _ Ω _ _ E _ _ D O Lt _ _ _ X B p q t hsm
  obtain ⟨C, C', hb⟩ := CuspWeightIntegrable.uFn_bound X
  have hω : X.omN B p q t = fun _ z => (q : ℝ)⁻¹ * Real.log ((X.NbarQ B p q t).h z) := by
    funext _ z
    simp [ComponentSetting.omN, div_eq_inv_mul]
  rw [hω]
  exact hM K ι (mCoordIdeal D.y) D.n X.M X.S.R (X.NbarQ B p q t) (q : ℝ)⁻¹ D.Bd (CuspWeightIntegrable.uFn X) C C'
    _ D.arith hsm (hBd II Ψ K ι Ω E D) (CuspWeightIntegrable.measurable_uFn X) hb
    (fun z hz hzb hY => CuspWeightIntegrable.cuspWeight_eq X hz hzb hY)

end GroundTheory.Heights₂.Heights.LowerBoundFree
