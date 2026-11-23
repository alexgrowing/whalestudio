import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnalyticLogResolution
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.LintegralImageEqLintegralNormSqDetMul
import ReciprocityTheory.AnalyticForms.PotentialTheory.Pullback
import ReciprocityTheory.AnalyticForms.PotentialTheory.Degree
import ReciprocityTheory.AnalyticForms.AnalyticCharts.NullZero

namespace GlobalTheory.TruncCoord

open GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions

noncomputable section

def truncCoord (n d : ℕ) : (Fin d → ℂ) →L[ℂ] (Fin n → ℂ) :=
  ContinuousLinearMap.pi fun k : Fin n =>
    if h : (k : ℕ) < d then ContinuousLinearMap.proj (⟨k, h⟩ : Fin d) else 0

theorem truncCoord_apply (n d : ℕ) (v : Fin d → ℂ) (k : Fin n) :
    truncCoord n d v k = if h : (k : ℕ) < d then v ⟨k, h⟩ else 0 := by
  unfold truncCoord
  by_cases h : (k : ℕ) < d <;> simp [h]

theorem truncCoord_padZero {n d : ℕ} (hnd : n ≤ d) (z : Fin n → ℂ) :
    truncCoord n d (padZero n d z) = z := by
  funext k
  have hk : (k : ℕ) < d := lt_of_lt_of_le k.2 hnd
  simp [truncCoord_apply, hk, padZero]

theorem padZero_truncCoord {n d : ℕ} (v : Fin d → ℂ) (hv : ∀ k : Fin d, n ≤ (k : ℕ) → v k = 0) :
    padZero n d (truncCoord n d v) = v := by
  funext k
  by_cases hk : (k : ℕ) < n
  · simp [padZero, hk, truncCoord_apply, k.2]
  · simp [padZero, hk, hv k (not_lt.1 hk)]

end

end GlobalTheory.TruncCoord

namespace GlobalTheory.RegToResolution

open MeasureTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions GlobalTheory.LogResInt GlobalTheory.TruncCoord
open scoped ENNReal

noncomputable section

theorem analyticAt_trunc_comp {d n : ℕ} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (A : FinHolAtlas d X) (Z : Set X) (ψ : OpenPartialHomeomorph X (Fin d → ℂ))
    (B : FinHolAtlas n Y) (μ : Y → X) (hμ : HoloMap B A μ) (j : Fin B.n) (w : Fin n → ℂ)
    (hψ : IsStraightening A Z n ψ) (hw : w ∈ (B.chart j).target)
    (hwψ : μ ((B.chart j).symm w) ∈ ψ.source) :
    AnalyticAt ℂ (fun w' => truncCoord n d (ψ (μ ((B.chart j).symm w')))) w := by
  obtain ⟨k, hk⟩ := A.cover (μ ((B.chart j).symm w))
  have hh : AnalyticAt ℂ (A.chart k ∘ μ ∘ (B.chart j).symm) w := hμ.2 j k w ⟨hw, hk⟩
  have hψk : AnalyticAt ℂ (ψ ∘ (A.chart k).symm) ((A.chart k ∘ μ ∘ (B.chart j).symm) w) :=
    (hψ.2.1 k).1 _ ⟨(A.chart k).map_source hk, by
      simp only [Function.comp_apply, Set.mem_preimage, (A.chart k).left_inv hk]; exact hwψ⟩
  have hc : AnalyticAt ℂ (truncCoord n d ∘ (ψ ∘ (A.chart k).symm) ∘ (A.chart k ∘ μ ∘ (B.chart j).symm)) w :=
    (truncCoord n d).analyticAt _ |>.comp (hψk.comp hh)
  refine hc.congr ?_
  filter_upwards [ReciprocityTheory.AnForm.M.holoMap_preimage_mem_nhds hμ j k hw hk] with w' hw'
  simp only [Function.comp_apply, (A.chart k).left_inv hw'.2]

theorem padZero_contDiff (n d : ℕ) : ContDiff ℝ ⊤ (padZero n d) := by
  refine contDiff_pi.2 fun k => ?_
  by_cases h : (k : ℕ) < n
  · have : (fun z : Fin n → ℂ => padZero n d z k) = fun z => z ⟨k, h⟩ := by
      funext z; simp [padZero, h]
    rw [this]; exact contDiff_apply ℝ ℂ _
  · have : (fun z : Fin n → ℂ => padZero n d z k) = fun _ => 0 := by
      funext z; simp [padZero, h]
    rw [this]; exact contDiff_const

theorem norm_locDens_pullback_eq {d n : ℕ} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (A : FinHolAtlas d X) (Z : Set X) (ψ : OpenPartialHomeomorph X (Fin d → ℂ))
    (B : FinHolAtlas n Y) (μ : Y → X) (hμ : HoloMap B A μ) (Φ : LocPot X) (j : Fin B.n)
    (w : Fin n → ℂ) (hψ : IsStraightening A Z n ψ) (hZ : Set.range μ ⊆ Z)
    (hw : w ∈ (B.chart j).target) (hwψ : μ ((B.chart j).symm w) ∈ ψ.source)
    (hsm : ∃ O : Set X, IsOpen O ∧ μ ((B.chart j).symm w) ∈ O ∧
      A.SmoothOn O (Φ.φ (μ ((B.chart j).symm w)))) :
    ‖locDens B (fun _ => Φ.pullback μ hμ.1) j w‖ =
      Complex.normSq (ReciprocityTheory.AnForm.A.jacC
        (fun w' => truncCoord n d (ψ (μ ((B.chart j).symm w')))) w).det *
      ‖paramDens n Φ ψ (truncCoord n d (ψ (μ ((B.chart j).symm w))))‖ := by
  obtain ⟨O, hO, hxO, hsmO⟩ := hsm
  set x0 := μ ((B.chart j).symm w) with hx0
  set τ : (Fin n → ℂ) → (Fin n → ℂ) := fun w' => truncCoord n d (ψ (μ ((B.chart j).symm w')))
    with hτ_def
  set g : (Fin n → ℂ) → ℝ := fun z' => Φ.φ x0 (param n ψ z') with hg_def

  have hpar : ∀ w', μ ((B.chart j).symm w') ∈ ψ.source →
      param n ψ (τ w') = μ ((B.chart j).symm w') := by
    intro w' hs
    have hz : μ ((B.chart j).symm w') ∈ Z ∩ ψ.source := ⟨hZ ⟨_, rfl⟩, hs⟩
    rw [hψ.2.2] at hz
    simp only [param, hτ_def]
    rw [padZero_truncCoord _ hz.2, ψ.left_inv hs]
  have hpadτ : padZero n d (τ w) = ψ x0 := by
    have hz : x0 ∈ Z ∩ ψ.source := ⟨hZ ⟨_, rfl⟩, hwψ⟩
    rw [hψ.2.2] at hz
    exact padZero_truncCoord _ hz.2
  have hτa : AnalyticAt ℂ τ w := analyticAt_trunc_comp A Z ψ B μ hμ j w hψ hw hwψ

  obtain ⟨k, hk⟩ := A.cover x0
  have hg2 : ContDiffAt ℝ 2 g (τ w) := by
    have h1 : ContDiffAt ℝ 2 (Φ.φ x0 ∘ (A.chart k).symm) (A.chart k x0) := by
      have hmem : (A.chart k).target ∩ (A.chart k).symm ⁻¹' O ∈ nhds (A.chart k x0) :=
        ((A.chart k).isOpen_inter_preimage_symm hO).mem_nhds
          ⟨(A.chart k).map_source hk, by simp only [Set.mem_preimage, (A.chart k).left_inv hk]; exact hxO⟩
      exact ((hsmO k).contDiffAt hmem).of_le (by first | exact_mod_cast (le_top : (2 : ℕ∞) ≤ ⊤) | simp | exact WithTop.coe_le_coe.2 le_top)
    have h2 : ContDiffAt ℝ 2 (A.chart k ∘ ψ.symm) (ψ x0) := by
      have ha : AnalyticAt ℂ (A.chart k ∘ ψ.symm) (ψ x0) :=
        (hψ.2.1 k).2 _ ⟨ψ.map_source hwψ, by simp only [Set.mem_preimage, ψ.left_inv hwψ]; exact hk⟩
      exact (ha.contDiffAt.restrict_scalars ℝ)
    have h3 : ContDiffAt ℝ 2 ((Φ.φ x0 ∘ (A.chart k).symm) ∘ (A.chart k ∘ ψ.symm) ∘ padZero n d) (τ w) := by
      have h23 : ContDiffAt ℝ 2 ((A.chart k ∘ ψ.symm) ∘ padZero n d) (τ w) := by
        refine ContDiffAt.comp (τ w) ?_ ((padZero_contDiff n d).contDiffAt.of_le le_top)
        rw [hpadτ]; exact h2
      refine ContDiffAt.comp (τ w) ?_ h23
      simp only [Function.comp_apply, hpadτ, ψ.left_inv hwψ]
      exact h1
    refine h3.congr_of_eventuallyEq ?_
    have hopen : IsOpen (padZero n d ⁻¹' (ψ.target ∩ ψ.symm ⁻¹' (A.chart k).source)) :=
      (ψ.isOpen_inter_preimage_symm (A.chart k).open_source).preimage (padZero_contDiff n d).continuous
    filter_upwards [hopen.mem_nhds (show τ w ∈ _ from by
      rw [Set.mem_preimage, hpadτ]
      exact ⟨ψ.map_source hwψ, by simp only [Set.mem_preimage, ψ.left_inv hwψ]; exact hk⟩)] with z hz
    simp only [hg_def, Function.comp_apply, param, (A.chart k).left_inv hz.2]

  have hev : (fun w' => Φ.φ x0 (μ ((B.chart j).symm w'))) =ᶠ[nhds w] g ∘ τ := by
    have hopen : IsOpen ((B.chart j).target ∩ (B.chart j).symm ⁻¹' (μ ⁻¹' ψ.source)) :=
      (B.chart j).isOpen_inter_preimage_symm (ψ.open_source.preimage hμ.1)
    filter_upwards [hopen.mem_nhds ⟨hw, hwψ⟩] with w' hw'
    simp only [Function.comp_apply, hg_def, hpar w' hw'.2]
  have hL : locDens B (fun _ => Φ.pullback μ hμ.1) j w = maDens (fun _ => g) (τ w) *
      Complex.normSq (ReciprocityTheory.AnForm.A.jacC τ w).det := by
    unfold locDens
    refine (maDens_congr_eventuallyEq (fun _ => hev)).trans ?_
    exact ReciprocityTheory.AnForm.A.maDens_comp (fun _ => g) τ w hτa (fun _ => hg2)
  have hP : paramDens n Φ ψ (τ w) = maDens (fun _ => g) (τ w) := by
    unfold paramDens
    rw [hpar w hwψ]
  rw [hL, hP, norm_mul, Real.norm_of_nonneg (Complex.normSq_nonneg _), mul_comm]

theorem padZero_eq_clm (n d : ℕ) : padZero n d = ⇑(ContinuousLinearMap.pi fun k : Fin d =>
    if h : (k : ℕ) < n then ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) (⟨k, h⟩ : Fin n)
    else (0 : (Fin n → ℂ) →L[ℂ] ℂ)) := by
  funext z k
  by_cases h : (k : ℕ) < n <;> simp [padZero, h]

theorem padZero_analyticAt (n d : ℕ) (z : Fin n → ℂ) : AnalyticAt ℂ (padZero n d) z := by
  rw [padZero_eq_clm]; exact ContinuousLinearMap.analyticAt _ _

theorem volume_param_preimage_null {d : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas d X)
    (Z : Set X) (n : ℕ) (ψ : OpenPartialHomeomorph X (Fin d → ℂ)) (S : Set X)
    (hψ : IsStraightening A Z n ψ) (hS : A.IsAnalyticSubset S) (hdense : Z ⊆ closure (Z \ S)) :
    volume {z : Fin n → ℂ | padZero n d z ∈ ψ.target ∧ param n ψ z ∈ S} = 0 := by
  have hpc : Continuous (padZero n d) := (padZero_contDiff n d).continuous
  apply ReciprocityTheory.AnForm.volume_eq_zero_of_locally_in_analytic_zero_set
  rintro z ⟨hzt, hzS⟩
  set x := param n ψ z with hx
  have hxs : x ∈ ψ.source := ψ.map_target hzt
  obtain ⟨W, hWo, hxW, r, f, hf, hSW⟩ := hS x
  obtain ⟨k, hk⟩ := A.cover x
  set U := padZero n d ⁻¹' (ψ.target ∩ ψ.symm ⁻¹' (W ∩ (A.chart k).source)) with hU
  have hUo : IsOpen U := (ψ.isOpen_inter_preimage_symm (hWo.inter (A.chart k).open_source)).preimage hpc
  have hzU : z ∈ U := ⟨hzt, hxW, hk⟩
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hUo z hzU

  have han : ∀ i, AnalyticOnNhd ℂ (fun z' => f i (param n ψ z')) (Metric.ball z ε) := by
    intro i z' hz'
    have hz'U := hball hz'
    have hp : param n ψ z' ∈ (A.chart k).source := hz'U.2.2
    have h1 : AnalyticAt ℂ (f i ∘ (A.chart k).symm) (((A.chart k ∘ ψ.symm) ∘ padZero n d) z') :=
      hf i k _ ⟨(A.chart k).map_source hp, by
        show (A.chart k).symm (A.chart k (param n ψ z')) ∈ W
        rw [(A.chart k).left_inv hp]; exact hz'U.2.1⟩
    have h2 : AnalyticAt ℂ (A.chart k ∘ ψ.symm) (padZero n d z') :=
      (hψ.2.1 k).2 _ ⟨hz'U.1, hz'U.2.2⟩
    have h3 : AnalyticAt ℂ ((f i ∘ (A.chart k).symm) ∘ (A.chart k ∘ ψ.symm) ∘ padZero n d) z' :=
      h1.comp (h2.comp (padZero_analyticAt n d z'))
    refine h3.congr ?_
    filter_upwards [hUo.mem_nhds hz'U] with z'' hz''
    simp only [Function.comp_apply, param, (A.chart k).left_inv hz''.2.2]

  have hex : ∃ i, ∃ w ∈ Metric.ball z ε, f i (param n ψ w) ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    set O := ψ.source ∩ ψ ⁻¹' (truncCoord n d ⁻¹' Metric.ball z ε) with hO
    have hOo : IsOpen O := ψ.isOpen_inter_preimage
      (Metric.isOpen_ball.preimage (truncCoord n d).continuous)
    have hψx : ψ x = padZero n d z := ψ.right_inv hzt
    have hxO : x ∈ O := ⟨hxs, by
      simp only [Set.mem_preimage, hψx, truncCoord_padZero hψ.1]; exact Metric.mem_ball_self hε⟩
    have hxZ : x ∈ Z := by
      have : x ∈ {y ∈ ψ.source | ∀ k : Fin d, n ≤ (k : ℕ) → ψ y k = 0} := by
        refine ⟨hxs, fun k hk' => ?_⟩
        rw [hψx]; simp [padZero, not_lt.2 hk']
      rw [← hψ.2.2] at this
      exact this.1
    obtain ⟨y, hyO, hyZ, hyS⟩ := mem_closure_iff.1 (hdense hxZ) O hOo hxO
    have hyt : ∀ k : Fin d, n ≤ (k : ℕ) → ψ y k = 0 := by
      have : y ∈ Z ∩ ψ.source := ⟨hyZ, hyO.1⟩
      rw [hψ.2.2] at this
      exact this.2
    set w := truncCoord n d (ψ y) with hw
    have hwb : w ∈ Metric.ball z ε := hyO.2
    have hpw : param n ψ w = y := by
      simp only [param, hw, padZero_truncCoord _ hyt, ψ.left_inv hyO.1]
    have hyW : y ∈ W := by rw [← hpw]; exact (hball hwb).2.1
    have : y ∈ S ∩ W := by
      rw [hSW]
      exact ⟨hyW, fun i => by rw [← hpw]; exact hcon i w hwb⟩
    exact hyS this.1
  obtain ⟨i, w, hwb, hne⟩ := hex
  refine ⟨Metric.ball z ε, Metric.isOpen_ball, Metric.mem_ball_self hε,
    (convex_ball z ε).isPreconnected, fun z' => f i (param n ψ z'), han i, ⟨w, hwb, hne⟩, ?_⟩
  rintro z' ⟨⟨-, hz'S⟩, hz'b⟩
  have : param n ψ z' ∈ S ∩ W := ⟨hz'S, (hball hz'b).2.1⟩
  rw [hSW] at this
  exact this.2 i

theorem measurableSet_inter_preimage {m : ℕ} {U : Set (Fin m → ℂ)} (hU : IsOpen U)
    {g : (Fin m → ℂ) → (Fin m → ℂ)} (hg : ContinuousOn g U) {s : Set (Fin m → ℂ)}
    (hs : MeasurableSet s) : MeasurableSet (U ∩ g ⁻¹' s) := by
  classical
  have hm : Measurable (U.piecewise g fun _ => 0) :=
    hg.measurable_piecewise continuousOn_const hU.measurableSet
  have : U ∩ g ⁻¹' s = U ∩ (U.piecewise g fun _ => 0) ⁻¹' s := by
    ext w
    constructor
    · rintro ⟨hw, hs⟩
      exact ⟨hw, by simpa [Set.piecewise_eq_of_mem _ _ _ hw] using hs⟩
    · rintro ⟨hw, hs⟩
      exact ⟨hw, by simpa [Set.piecewise_eq_of_mem _ _ _ hw] using hs⟩
  rw [this]
  exact hU.measurableSet.inter (hm hs)

theorem regIntegral_le_chartSumInt :
    ∀ (d : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (A : FinHolAtlas d X) (Z : Set X) (n : ℕ) (Y : Type) [TopologicalSpace Y] [CompactSpace Y] [T2Space Y]
    (B : FinHolAtlas n Y) (μ : Y → X) (hμ : HoloMap B A μ) (S V : Set X),
    Set.range μ = Z → A.IsAnalyticSubset S → Z ⊆ closure (Z \ S) → Set.InjOn μ (μ ⁻¹' S)ᶜ →
    (∀ y, y ∉ μ ⁻¹' S → ∀ j, y ∈ (B.chart j).source → ∀ v : Fin n → ℂ,
      fderiv ℂ (fun w => A.chart (chartIdx A (μ y)) (μ ((B.chart j).symm w))) (B.chart j y) v = 0 →
        v = 0) →
    (∀ y, ∃ χ : OpenPartialHomeomorph Y (Fin n → ℂ), IsCompatChart B χ ∧ y ∈ χ.source ∧
      ∃ J : Finset (Fin n), μ ⁻¹' S ∩ χ.source = {w ∈ χ.source | ∃ a ∈ J, χ w a = 0}) →
    ∀ Φ : LocPot X, (∀ x, x ∉ V → ∃ O : Set X, IsOpen O ∧ x ∈ O ∧ O ⊆ Φ.U x ∧ A.SmoothOn O (Φ.φ x)) →
    ∀ f : X → ℝ≥0∞,
    regIntegral A Z n Φ (regularLocus A Z n \ V) f ≤
      chartSumInt B (Φ.pullback μ hμ.1) (μ ⁻¹' V)ᶜ (fun y => f (μ y)) := by
  intro d X _ _ _ A Z n Y _ _ _ B μ hμ S V hrange hS hdense hinj _ _ Φ hΦ f
  have hSc : IsClosed S := isClosed_of_isAnalyticSubset A hS
  unfold regIntegral
  refine iSup_le fun k => iSup_le fun ψ => iSup_le fun Bp => iSup_le fun hP => ?_

  set m : Fin B.n → (Fin n → ℂ) → X := fun j w => μ ((B.chart j).symm w) with hm_def
  set τ : Fin k → Fin B.n → (Fin n → ℂ) → (Fin n → ℂ) :=
    fun i j w => truncCoord n d (ψ i (m j w)) with hτ_def
  set E : Fin k → Fin B.n → Set (Fin n → ℂ) := fun i j =>
    (B.chart j).target ∩ m j ⁻¹' ((ψ i).source ∩ Sᶜ) ∩ τ i j ⁻¹' Bp i with hE_def
  set N : Fin k → Set (Fin n → ℂ) :=
    fun i => {z | padZero n d z ∈ (ψ i).target ∧ param n (ψ i) z ∈ S} with hN_def
  set F : Fin k → (Fin n → ℂ) → ℝ≥0∞ :=
    fun i z => f (param n (ψ i) z) * ‖paramDens n Φ (ψ i) z‖ₑ with hF_def
  set G : Fin B.n → (Fin n → ℂ) → ℝ≥0∞ :=
    fun j w => f (m j w) * ‖locDens B (fun _ => Φ.pullback μ hμ.1) j w‖ₑ with hG_def
  have hψ : ∀ i, IsStraightening A Z n (ψ i) := hP.1
  have hmc : ∀ j, ContinuousOn (m j) (B.chart j).target := fun j =>
    hμ.1.comp_continuousOn (B.chart j).continuousOn_symm

  have hparam : ∀ i j w, m j w ∈ (ψ i).source → param n (ψ i) (τ i j w) = m j w := by
    intro i j w hs
    have hZ : m j w ∈ Z ∩ (ψ i).source := ⟨hrange ▸ ⟨_, rfl⟩, hs⟩
    rw [(hψ i).2.2] at hZ
    simp only [param, hτ_def]
    rw [padZero_truncCoord _ hZ.2, (ψ i).left_inv hs]
  have hOpen : ∀ i j, IsOpen ((B.chart j).target ∩ m j ⁻¹' ((ψ i).source ∩ Sᶜ)) := fun i j =>
    (hmc j).isOpen_inter_preimage (B.chart j).open_target
      ((ψ i).open_source.inter hSc.isOpen_compl)
  have hmeas : ∀ i j, MeasurableSet (E i j) := by
    intro i j
    refine measurableSet_inter_preimage (hOpen i j) ?_ (hP.2.1 i)
    refine (truncCoord n d).continuous.comp_continuousOn ?_
    exact (ψ i).continuousOn.comp ((hmc j).mono Set.inter_subset_left)
      (fun w hw => hw.2.1)
  have hinjE : ∀ i j, Set.InjOn (τ i j) (E i j) := by
    intro i j w₁ h₁ w₂ h₂ heq
    have e₁ := hparam i j w₁ h₁.1.2.1
    have e₂ := hparam i j w₂ h₂.1.2.1
    have hme : m j w₁ = m j w₂ := by rw [← e₁, ← e₂, heq]
    have hy : (B.chart j).symm w₁ = (B.chart j).symm w₂ :=
      hinj (fun h => h₁.1.2.2 h) (fun h => h₂.1.2.2 h) hme
    exact (B.chart j).symm.injOn h₁.1.1 h₂.1.1 hy
  have han : ∀ i j, ∀ w ∈ E i j, AnalyticAt ℂ (τ i j) w := fun i j w hw =>
    analyticAt_trunc_comp A Z (ψ i) B μ hμ j w (hψ i) hw.1.1 hw.1.2.1
  have hnotV : ∀ i j, ∀ w ∈ E i j, m j w ∉ V := by
    intro i j w hw
    have h := ((hP.2.2.1 i (τ i j w) hw.2).2).2
    rwa [hparam i j w hw.1.2.1] at h
  have hdens : ∀ i j, ∀ w ∈ E i j,
      ENNReal.ofReal (Complex.normSq (ReciprocityTheory.AnForm.A.jacC (τ i j) w).det) * F i (τ i j w) =
        G j w := by
    intro i j w hw
    obtain ⟨O, hO, hxO, -, hsm⟩ := hΦ (m j w) (hnotV i j w hw)
    have h := norm_locDens_pullback_eq A Z (ψ i) B μ hμ Φ j w (hψ i) hrange.le hw.1.1 hw.1.2.1
      ⟨O, hO, hxO, hsm⟩
    simp only [hF_def, hG_def]
    rw [hparam i j w hw.1.2.1, ← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, h,
      ENNReal.ofReal_mul (Complex.normSq_nonneg _)]
    ring
  have hcov : ∀ i, Bp i \ N i ⊆ ⋃ j, τ i j '' E i j := by
    intro i z ⟨hzB, hzN⟩
    have hzt := (hP.2.2.1 i z hzB).1
    have hzS : param n (ψ i) z ∉ S := fun h => hzN ⟨hzt, h⟩
    obtain ⟨y, hy⟩ : param n (ψ i) z ∈ Set.range μ :=
      hrange ▸ (hP.2.2.1 i z hzB).2.1.1
    obtain ⟨j, hj⟩ := B.cover y
    have hmw : m j (B.chart j y) = param n (ψ i) z := by
      simp only [hm_def, (B.chart j).left_inv hj, hy]
    have hsrc : param n (ψ i) z ∈ (ψ i).source := (ψ i).map_target hzt
    have hτw : τ i j (B.chart j y) = z := by
      simp only [hτ_def, hmw, param, (ψ i).right_inv hzt]
      exact truncCoord_padZero (hψ i).1 z
    refine Set.mem_iUnion.2 ⟨j, B.chart j y, ⟨⟨(B.chart j).map_source hj, ?_⟩, ?_⟩, hτw⟩
    · rw [Set.mem_preimage, hmw]; exact ⟨hsrc, hzS⟩
    · rw [Set.mem_preimage, hτw]; exact hzB
  have hdisj : ∀ j, Pairwise (Function.onFun Disjoint fun i => E i j) := by
    intro j i i' hii'
    refine Set.disjoint_left.2 fun w hw hw' => ?_
    have h1 : m j w ∈ param n (ψ i) '' Bp i := ⟨_, hw.2, hparam i j w hw.1.2.1⟩
    have h2 : m j w ∈ param n (ψ i') '' Bp i' := ⟨_, hw'.2, hparam i' j w hw'.1.2.1⟩
    exact Set.disjoint_left.1 (hP.2.2.2 hii') h1 h2
  have hsub : ∀ j, (⋃ i, E i j) ⊆ (B.chart j).target ∩ (B.chart j).symm ⁻¹' (μ ⁻¹' V)ᶜ := by
    intro j w hw
    obtain ⟨i, hw⟩ := Set.mem_iUnion.1 hw
    exact ⟨hw.1.1, hnotV i j w hw⟩

  have hpiece : ∀ i, ∫⁻ z in Bp i, F i z ≤ ∑ j, ∫⁻ w in E i j, G j w := by
    intro i
    have hN0 : volume (N i) = 0 :=
      volume_param_preimage_null A Z n (ψ i) S (hψ i) hS hdense
    calc ∫⁻ z in Bp i, F i z = ∫⁻ z in Bp i \ N i, F i z :=
          (setLIntegral_congr (diff_null_ae_eq_self hN0)).symm
      _ ≤ ∫⁻ z in ⋃ j, τ i j '' E i j, F i z := lintegral_mono_set (hcov i)
      _ ≤ ∑' j, ∫⁻ z in τ i j '' E i j, F i z := lintegral_iUnion_le _ _
      _ = ∑ j, ∫⁻ z in τ i j '' E i j, F i z := tsum_fintype _
      _ = ∑ j, ∫⁻ w in E i j, G j w := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume (hmeas i j)
            (fun w hw => ((han i j w hw).differentiableAt.restrictScalars ℝ).hasFDerivAt.hasFDerivWithinAt)
            (hinjE i j) (F i)]
          refine setLIntegral_congr_fun (hmeas i j) fun w hw => ?_
          rw [ReciprocityTheory.AnForm.A.det_fderiv_real_eq_normSq _ _ (han i j w hw).differentiableAt,
            abs_of_nonneg (Complex.normSq_nonneg _)]
          exact hdens i j w hw
  calc ∑ i, ∫⁻ z in Bp i, f (param n (ψ i) z) * ‖paramDens n Φ (ψ i) z‖ₑ
        = ∑ i, ∫⁻ z in Bp i, F i z := rfl
    _ ≤ ∑ i, ∑ j, ∫⁻ w in E i j, G j w := Finset.sum_le_sum fun i _ => hpiece i
    _ = ∑ j, ∑ i, ∫⁻ w in E i j, G j w := Finset.sum_comm
    _ = ∑ j, ∫⁻ w in ⋃ i, E i j, G j w := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [lintegral_iUnion (fun i => hmeas i j) (hdisj j), tsum_fintype]
    _ ≤ ∑ j, ∫⁻ w in (B.chart j).target ∩ (B.chart j).symm ⁻¹' (μ ⁻¹' V)ᶜ, G j w :=
        Finset.sum_le_sum fun j _ => lintegral_mono_set (hsub j)
    _ = chartSumInt B (Φ.pullback μ hμ.1) (μ ⁻¹' V)ᶜ (fun y => f (μ y)) := rfl

end

end GlobalTheory.RegToResolution
