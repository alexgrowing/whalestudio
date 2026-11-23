import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FirstChernLeviEqConstant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedIntegralCutoffLogDecayStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TailLogIntegralBoundOfDistributionStatement
import ReciprocityTheory.AnalyticForms.PotentialTheory.DegreeIntA
import ReciprocityTheory.AnalyticForms.PotentialTheory.MaMeasureB
import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffAtOfIsPotential

open MvPolynomial Formalism.DegreeFormula Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.MainNotions.WeightThresholdDefs Filter Topology Classical
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.FlagPoly GlobalTheory.FlagAr GlobalTheory.Mean4 GlobalTheory.Mean4O
open MeasureTheory

noncomputable section

namespace GlobalTheory.Mean4O.LogTail

variable {e : ℕ} {X : Type} [TopologicalSpace X]

def PotOff (A : FinHolAtlas e X) (Z : Set X) (P : LocPot X) : Prop :=
  (∀ x, A.SmoothOn (P.U x ∩ Zᶜ) (P.φ x)) ∧
  ∀ x x', ∀ y ∈ P.U x ∩ P.U x', ∃ W : Set X, IsOpen W ∧ y ∈ W ∧ ∃ G : X → ℂ,
    A.HoloOn W G ∧ ∀ z ∈ W ∩ P.U x ∩ P.U x', P.φ x z - P.φ x' z = (G z).re

theorem potOff_of_listForm {A : FinHolAtlas e X} {Z : Set X} {r : X → ℝ} {Om : LocPot X} {K : ℝ} {T : LocPot X}
    (h : ListForm A Z r Om K T) : PotOff A Z T := by
  obtain ⟨θ, u, rfl, hθ, -, -, hu, -⟩ := h
  refine ⟨fun x j => ?_, fun x x' y hy => ?_⟩
  · exact ((hθ.1 x j).mono fun y hy => ⟨hy.1, hy.2.1.1⟩).add ((hu j).mono fun y hy => ⟨hy.1, hy.2.2⟩)
  · obtain ⟨W, hW, hyW, G, hG, hGe⟩ := hθ.2 x x' y ⟨hy.1.1, hy.2.1⟩
    refine ⟨W, hW, hyW, G, hG, fun z hz => ?_⟩
    have := hGe z ⟨⟨hz.1.1, hz.1.2.1⟩, hz.2.1⟩
    show (θ.φ x z + u z) - (θ.φ x' z + u z) = _
    linarith

theorem PotOff.smoothAt {A : FinHolAtlas e X} {Z : Set X} (hZ : IsClosed Z) {P : LocPot X} (hP : PotOff A Z P)
    (x : X) (j : Fin A.n) {y : Fin e → ℂ} (hy : y ∈ (A.chart j).target) (hU : (A.chart j).symm y ∈ P.U x)
    (hyZ : (A.chart j).symm y ∉ Z) : ContDiffAt ℝ 2 (P.φ x ∘ (A.chart j).symm) y :=
  ((hP.1 x j).contDiffAt
    (((A.chart j).isOpen_inter_preimage_symm ((P.isOpen_U x).inter hZ.isOpen_compl)).mem_nhds ⟨hy, hU, hyZ⟩)).of_le
    (WithTop.coe_le_coe.2 le_top)

theorem dens_base {A : FinHolAtlas e X} {Z : Set X} (hZ : IsClosed Z) {Φ : Fin e → LocPot X}
    (hΦ : ∀ i, PotOff A Z (Φ i)) (j : Fin A.n) {y : Fin e → ℂ} (hy : y ∈ (A.chart j).target)
    (hyZ : (A.chart j).symm y ∉ Z) (x : X) (hx : ∀ i, (A.chart j).symm y ∈ (Φ i).U x) :
    locDens A Φ j y = maDens (fun i y' => (Φ i).φ x ((A.chart j).symm y')) y := by
  unfold locDens
  apply maDens_congr_hessC
  intro i
  obtain ⟨W, hWo, hyW, G, hG, hGeq⟩ :=
    (hΦ i).2 ((A.chart j).symm y) x ((A.chart j).symm y) ⟨(Φ i).mem_U _, hx i⟩
  have hVo : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹'
      (W ∩ (Φ i).U ((A.chart j).symm y) ∩ (Φ i).U x)) :=
    (A.chart j).isOpen_inter_preimage_symm
      ((hWo.inter ((Φ i).isOpen_U _)).inter ((Φ i).isOpen_U x))
  have hyV : y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹'
      (W ∩ (Φ i).U ((A.chart j).symm y) ∩ (Φ i).U x) :=
    ⟨hy, ⟨⟨hyW, (Φ i).mem_U _⟩, hx i⟩⟩
  have h1 : (fun y' => (Φ i).φ ((A.chart j).symm y) ((A.chart j).symm y')) =ᶠ[nhds y]
      (fun w => ((Φ i).φ x ∘ (A.chart j).symm) w + ((G ∘ (A.chart j).symm) w).re) := by
    filter_upwards [hVo.mem_nhds hyV] with w hw
    have := hGeq ((A.chart j).symm w) hw.2
    simp only [Function.comp_apply]
    linarith
  rw [hessCGerm _ _ _ h1]
  exact ReciprocityTheory.AnForm.A.hessC_add_re_analytic _ _ _
    ((hΦ i).smoothAt hZ x j hy (hx i) hyZ) (hG j y ⟨hy, hyW⟩)

theorem dens_cont {A : FinHolAtlas e X} {Z : Set X} (hZ : IsClosed Z) {Φ : Fin e → LocPot X}
    (hΦ : ∀ i, PotOff A Z (Φ i)) (j : Fin A.n) :
    ContinuousOn (locDens A Φ j) ((A.chart j).target ∩ (A.chart j).symm ⁻¹' Zᶜ) := by
  intro y0 hy0
  apply ContinuousAt.continuousWithinAt
  have hVo : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹'
      ((⋂ i, (Φ i).U ((A.chart j).symm y0)) ∩ Zᶜ)) :=
    (A.chart j).isOpen_inter_preimage_symm
      ((isOpen_iInter_of_finite fun i => (Φ i).isOpen_U _).inter hZ.isOpen_compl)
  have hy0V : y0 ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹'
      ((⋂ i, (Φ i).U ((A.chart j).symm y0)) ∩ Zᶜ) :=
    ⟨hy0.1, Set.mem_iInter.2 fun i => (Φ i).mem_U _, hy0.2⟩
  have heq : maDens (fun i y' => (Φ i).φ ((A.chart j).symm y0) ((A.chart j).symm y')) =ᶠ[nhds y0]
      locDens A Φ j := by
    filter_upwards [hVo.mem_nhds hy0V] with y hy
    exact (dens_base hZ hΦ j hy.1 hy.2.2 _ (fun i => Set.mem_iInter.1 hy.2.1 i)).symm
  refine ContinuousAt.congr ?_ heq
  refine (maDens_continuousOn _ _ hVo fun i => ?_).continuousAt (hVo.mem_nhds hy0V)
  exact (((hΦ i).1 _ j).of_le (WithTop.coe_le_coe.2 le_top)).mono
    fun y hy => ⟨hy.1, Set.mem_iInter.1 hy.2.1 i, hy.2.2⟩

theorem dens_chart {A : FinHolAtlas e X} {Z : Set X} (hZ : IsClosed Z) {Φ : Fin e → LocPot X}
    (hΦ : ∀ i, PotOff A Z (Φ i)) (j k : Fin A.n) (y : Fin e → ℂ) (hy : y ∈ (A.chart j).target)
    (hyk : (A.chart j).symm y ∈ (A.chart k).source) (hyZ : (A.chart j).symm y ∉ Z) :
    locDens A Φ j y = locDens A Φ k (A.chart k ((A.chart j).symm y)) *
        ‖LinearMap.det (fderiv ℂ (A.chart k ∘ (A.chart j).symm) y :
          (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ))‖ ^ 2 := by
  have hτ : AnalyticAt ℂ (A.chart k ∘ (A.chart j).symm) y := A.holo j k y ⟨hy, hyk⟩
  have hsk : (A.chart k).symm (A.chart k ((A.chart j).symm y)) = (A.chart j).symm y :=
    (A.chart k).left_inv hyk
  have htk : A.chart k ((A.chart j).symm y) ∈ (A.chart k).target := (A.chart k).map_source hyk
  have hL : locDens A Φ k (A.chart k ((A.chart j).symm y)) =
      maDens (fun i y' => (Φ i).φ ((A.chart j).symm y) ((A.chart k).symm y'))
        (A.chart k ((A.chart j).symm y)) := by
    simp only [locDens, hsk]
  have hsm : ∀ i, ContDiffAt ℝ 2 (fun y' => (Φ i).φ ((A.chart j).symm y) ((A.chart k).symm y'))
      ((A.chart k ∘ (A.chart j).symm) y) := fun i =>
    (hΦ i).smoothAt hZ ((A.chart j).symm y) k htk (by rw [Function.comp_apply, hsk]; exact (Φ i).mem_U _)
      (by rw [Function.comp_apply, hsk]; exact hyZ)
  have hcomp := ReciprocityTheory.AnForm.A.maDens_comp
    (fun i y' => (Φ i).φ ((A.chart j).symm y) ((A.chart k).symm y'))
    (A.chart k ∘ (A.chart j).symm) y hτ hsm
  rw [ReciprocityTheory.AnForm.A.det_jacC, Complex.normSq_eq_norm_sq] at hcomp
  have key : locDens A Φ j y = maDens (fun i =>
      (fun y' => (Φ i).φ ((A.chart j).symm y) ((A.chart k).symm y')) ∘
        (A.chart k ∘ (A.chart j).symm)) y := by
    unfold locDens
    apply maDens_congr_hessC
    intro i
    apply hessCGerm
    have hWo : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (A.chart k).source) :=
      (A.chart j).isOpen_inter_preimage_symm (A.chart k).open_source
    filter_upwards [hWo.mem_nhds (show y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' (A.chart k).source
      from ⟨hy, hyk⟩)] with w hw
    simp only [Function.comp_apply]
    rw [(A.chart k).left_inv hw.2]
  rw [hL, key]
  exact hcomp

theorem dens_nonneg {A : FinHolAtlas e X} {Z : Set X} (hZ : IsClosed Z) {Φ : Fin e → LocPot X}
    (hΦ : ∀ i, PotOff A Z (Φ i)) (hp : ∀ i, PshOff A Z (Φ i)) (j : Fin A.n) {y : Fin e → ℂ}
    (hy : y ∈ (A.chart j).target) (hyZ : (A.chart j).symm y ∉ Z) : 0 ≤ locDens A Φ j y :=
  ReciprocityTheory.AnForm.A.maDens_nonneg_of_posSemidef _ y fun i =>
    hessC_posSemidef_of_levi _ y ((hΦ i).smoothAt hZ _ j hy ((Φ i).mem_U _) hyZ) (hp i j y hy hyZ)

theorem exists_measure [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
    {A : FinHolAtlas e X} {Z : Set X} (hZ : IsClosed Z) {Φ : Fin e → LocPot X}
    (hΦ : ∀ i, PotOff A Z (Φ i)) (hp : ∀ i, PshOff A Z (Φ i)) :
    ∃ μ : Measure X, ∀ g : X → ℝ, Measurable g → (∀ x ∈ Z, g x = 0) →
      (MIntegrable A Φ g ↔ Integrable g μ) ∧ (Integrable g μ → mInt A Φ g = ∫ x, g x ∂μ) := by
  have hne : Nonempty (ChartPartition A) := existsPartition A
  set P := hne.some with hP
  have hO : ∀ j, IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' Zᶜ) := fun j =>
    (A.chart j).isOpen_inter_preimage_symm hZ.isOpen_compl
  refine ⟨∑ j, ((volume.restrict ((A.chart j).target ∩ (A.chart j).symm ⁻¹' Zᶜ)).withDensity fun y =>
    ENNReal.ofReal (P.χ j ((A.chart j).symm y) * locDens A Φ j y)).map (A.chart j).symm, fun g hg hg0 => ?_⟩
  have key := fun j => map_withDensity_integrable_integral
    (w := fun y => P.χ j ((A.chart j).symm y) * locDens A Φ j y) (hO j)
    ((A.chart j).continuousOn_symm.mono Set.inter_subset_left)
    (((chi_comp_continuousOn P j).mono Set.inter_subset_left).mul (dens_cont hZ hΦ j))
    (fun y hy => mul_nonneg (P.nonneg j _) (dens_nonneg hZ hΦ hp j hy.1 hy.2)) hg
  have hz : ∀ j, ∀ y ∈ (A.chart j).target \ ((A.chart j).target ∩ (A.chart j).symm ⁻¹' Zᶜ),
      g ((A.chart j).symm y) = 0 := fun j y hy => hg0 _ (by
    by_contra h
    exact hy.2 ⟨hy.1, h⟩)
  rw [integrable_finsetSum_measure]
  refine ⟨⟨fun h j _ => (key j).1.2 ?_, fun h => ?_⟩, fun h => ?_⟩
  · refine ((integrableOn_weight A P Φ g h j).mono_set Set.inter_subset_left).congr_fun
      (fun y _ => ?_) (hO j).measurableSet
    ring
  · have hD : DIChartDens A (fun j y => if (A.chart j).symm y ∈ Z then 0 else locDens A Φ j y) := by
      intro a b z hz hz2
      simp only [(A.chart b).left_inv hz2]
      split_ifs with h'
      · simp
      · exact dens_chart hZ hΦ a b z hz hz2 h'
    have h2 := dI_target_of_weights A P hD g (fun j => ?_)
    · intro j K hK hKc
      refine ((h2 j).mono_set hK).congr_fun (fun y _ => ?_) hKc.measurableSet
      by_cases h' : (A.chart j).symm y ∈ Z
      · simp [hg0 _ h']
      · simp [h']
    · refine IntegrableOn.of_forall_sdiff_eq_zero (s := (A.chart j).target ∩ (A.chart j).symm ⁻¹' Zᶜ) ?_
        (A.chart j).open_target.measurableSet (fun y hy => by simp [hz j y hy])
      refine ((key j).1.1 (h j (Finset.mem_univ j))).congr_fun (fun y hy => ?_) (hO j).measurableSet
      have h' : (A.chart j).symm y ∉ Z := hy.2
      simp only [h', if_false]
      ring
  · rw [integral_finsetSum_measure h, mInt_eq_integralWith A Φ hne]
    unfold integralWith
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [(key j).2, setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (A.chart j).open_target.measurableSet
      (Set.inter_subset_left (t := (A.chart j).symm ⁻¹' Zᶜ)) (fun y hy => by simp [hz j y hy])]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only
    ring

theorem listForm_mono {A : FinHolAtlas e X} {Z : Set X} {r : X → ℝ} {Om : LocPot X} (hb : IsBd A Z r Om)
    {K K' : ℝ} (hK : K ≤ K') {T : LocPot X} (h : ListForm A Z r Om K T) : ListForm A Z r Om K' T := by
  obtain ⟨-, -, hOm, hpos, -, hr, -⟩ := hb
  have hpsh : IsPsh A Om := fun x j y hy w => by
    by_cases hw : w = 0
    · simp [hw, levi]
    · exact (hpos x j y hy w hw).le
  have aux : ∀ θ : LocPot X, IsPotential A θ → IsPsh A (Om.rsmul K + θ) → IsPsh A (Om.rsmul K' + θ) := by
    intro θ hθ h x j y hy w
    have h1 := isPshAdd A _ _ (isPotentialRsmul A (K' - K) Om hOm)
      (isPotentialAdd A _ _ (isPotentialRsmul A K Om hOm) hθ)
      (isPshRsmul A (K' - K) Om (by linarith) hOm hpsh) h x j y ⟨hy.1, hy.2.1, hy.2⟩ w
    have h2 : (Om.rsmul (K' - K) + (Om.rsmul K + θ)).φ x = (Om.rsmul K' + θ).φ x := by
      funext z
      show (K' - K) * Om.φ x z + (K * Om.φ x z + θ.φ x z) = K' * Om.φ x z + θ.φ x z
      ring
    rwa [h2] at h1
  obtain ⟨θ, u, hT, hθ, h1, h2, hu, hb, h3⟩ := h
  refine ⟨θ, u, hT, hθ, aux θ hθ h1, aux _ (isPotentialRsmul A _ θ hθ) h2, hu, fun x hx => ⟨?_, (hb x hx).2⟩, h3⟩
  have hl : 0 ≤ Real.log (r x) := Real.log_nonneg ((Real.one_le_exp zero_le_one).trans (hr x hx))
  have := mul_le_mul_of_nonneg_right hK hl
  linarith [(hb x hx).1]

theorem measurable_off [MeasurableSpace X] [BorelSpace X] {A : FinHolAtlas e X} {Z : Set X} (hZ : IsClosed Z)
    {r : X → ℝ} (hr : A.SmoothOn Zᶜ r) : Measurable (Zᶜ.indicator r) := by
  have hc : ContinuousOn r Zᶜ := by
    intro x hx
    apply ContinuousAt.continuousWithinAt
    obtain ⟨j, hj⟩ := A.cover x
    have h2 : ContinuousAt (r ∘ (A.chart j).symm) (A.chart j x) :=
      (hr j).continuousOn.continuousAt (((A.chart j).isOpen_inter_preimage_symm hZ.isOpen_compl).mem_nhds
        ⟨(A.chart j).map_source hj, by simpa [(A.chart j).left_inv hj] using hx⟩)
    have h3 : ContinuousAt ((r ∘ (A.chart j).symm) ∘ (A.chart j)) x :=
      h2.comp ((A.chart j).continuousAt hj)
    refine h3.congr ?_
    filter_upwards [(A.chart j).open_source.mem_nhds hj] with z hz
    simp [(A.chart j).left_inv hz]
  rw [← Set.piecewise_eq_indicator]
  exact hc.measurable_piecewise continuousOn_const hZ.isOpen_compl.measurableSet

theorem tail : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X) (Z : Set X)
    (r : X → ℝ) (Om : LocPot X), IsBd A Z r Om → ∀ K : ℝ, ∃ C : ℝ, Tail A Z r Om K C := by
  intro e X _ _ _ A Z r Om hb K
  borelize X
  obtain ⟨C, hC⟩ := GlobalTheory.T.mixed_integral_cutoff_log_decay e X A Z r Om hb (max K 1) (le_max_right _ _)
  set c : ℝ := ∑' k : ℕ, ((k : ℝ) + 2) ^ (e + 1) / 2 ^ k with hc
  have hc0 : 0 ≤ c := tsum_nonneg fun k => by positivity
  refine ⟨max C (max C 0 * c), fun T hT => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hC T fun i => listForm_mono hb (le_max_left _ _) (hT i)
  have hZ : IsClosed Z := hb.1
  have hre : ∀ x, x ∉ Z → Real.exp 1 ≤ r x := hb.2.2.2.2.2.1
  have hm : Measurable (Zᶜ.indicator r) := measurable_off hZ hb.2.2.2.2.1
  obtain ⟨μ, hμ⟩ := exists_measure hZ (fun i => potOff_of_listForm (hT i))
    (fun i => by obtain ⟨_, _, h⟩ := hT i; exact h.2.2.2.2.2.2.2)
  have hset : ∀ R : ℝ, Real.exp 1 ≤ R → {x | R ≤ Zᶜ.indicator r x} = {x | R ≤ r x} ∩ Zᶜ := by
    intro R hR
    have hR0 : 0 < R := (Real.exp_pos 1).trans_le hR
    ext x
    by_cases hx : x ∈ Z
    · simp [hx, hR0]
    · simp [hx]
  have hms : ∀ R : ℝ, MeasurableSet {x | R ≤ Zᶜ.indicator r x} := fun R => measurableSet_le measurable_const hm
  have hcut0 : ∀ (S : Set X) (f : X → ℝ), ∀ x ∈ Z, cut Z S f x = 0 := fun S f x hx =>
    Set.indicator_of_notMem (fun h => h.2 hx) _
  have huniv : ∀ f : X → ℝ, cut Z Set.univ f = cut Z {x | Real.exp 1 ≤ r x} f := by
    intro f
    unfold cut
    congr 1
    ext x
    exact ⟨fun h => ⟨hre x h.2, h.2⟩, fun h => ⟨trivial, h.2⟩⟩
  have hm1 : ∀ R : ℝ, Real.exp 1 ≤ R → Measurable (cut Z {x | R ≤ r x} fun _ => (1 : ℝ)) := fun R hR => by
    unfold cut
    rw [← hset R hR]
    exact measurable_const.indicator (hms R)
  have hi1 : Integrable (cut Z {x | Real.exp 1 ≤ r x} fun _ => (1 : ℝ)) μ :=
    (hμ _ (hm1 _ le_rfl) (hcut0 _ _)).1.1 (huniv _ ▸ h1)
  have hiR : ∀ R : ℝ, Real.exp 1 ≤ R → Integrable (cut Z {x | R ≤ r x} fun _ => (1 : ℝ)) μ := fun R hR => by
    refine hi1.mono (hm1 R hR).aestronglyMeasurable (Eventually.of_forall fun x => ?_)
    unfold cut
    have hs : {x | R ≤ r x} ∩ Zᶜ ⊆ {x | Real.exp 1 ≤ r x} ∩ Zᶜ := fun y hy => ⟨hR.trans hy.1, hy.2⟩
    exact norm_indicator_le_of_subset hs _ _
  have hmass : ∀ ρ : ℝ, Real.exp 1 ≤ ρ →
      μ {x | ρ ≤ Zᶜ.indicator r x} ≤ ENNReal.ofReal (max C 0 * Real.log ρ ^ e / ρ) := by
    intro ρ hρ
    have hρ0 : 0 < ρ := (Real.exp_pos 1).trans_le hρ
    have hl : 0 ≤ Real.log ρ := Real.log_nonneg ((Real.one_le_exp zero_le_one).trans hρ)
    have e1 := (hμ _ (hm1 ρ hρ) (hcut0 _ _)).2 (hiR ρ hρ)
    have e2 := h3 ρ hρ
    have hI := hiR ρ hρ
    rw [e1] at e2
    unfold cut at e2 hI
    rw [← hset ρ hρ] at e2 hI
    have hfin : μ {x | ρ ≤ Zᶜ.indicator r x} ≠ ⊤ := by
      rw [integrable_indicator_iff (hms ρ), integrableOn_const_iff] at hI
      simpa [lt_top_iff_ne_top] using hI
    rw [integral_indicator (hms ρ)] at e2
    simp only [integral_const, MeasurableSet.univ, measureReal_restrict_apply, Set.univ_inter, smul_eq_mul,
      mul_one] at e2
    rw [← ENNReal.ofReal_toReal hfin]
    refine ENNReal.ofReal_le_ofReal (e2.trans ?_)
    gcongr
    exact le_max_left _ _
  have hlog : ∀ R : ℝ, Real.exp 1 ≤ R → MIntegrable A T (cut Z {x | R ≤ r x} fun x => Real.log (r x)) ∧
      mInt A T (cut Z {x | R ≤ r x} fun x => Real.log (r x)) ≤ max C 0 * c * Real.log R ^ (e + 1) / R := by
    intro R hR
    have hR0 : 0 < R := (Real.exp_pos 1).trans_le hR
    have hR1 : 1 ≤ R := (Real.one_le_exp zero_le_one).trans hR
    have hl : 0 ≤ Real.log R := Real.log_nonneg hR1
    have hs := GlobalTheory.T.tail_log_integral_bound_of_distribution X μ _ e (max C 0) R hm (le_max_right _ _) hR fun ρ hρ => hmass ρ (hR.trans hρ)
    have heq : (cut Z {x | R ≤ r x} fun x => Real.log (r x)) =
        {x | R ≤ Zᶜ.indicator r x}.indicator fun x => Real.log (Zᶜ.indicator r x) := by
      rw [hset R hR]
      unfold cut
      refine Set.indicator_congr fun x hx => ?_
      simp only [Set.indicator_of_mem hx.2]
    have hmg : Measurable (cut Z {x | R ≤ r x} fun x => Real.log (r x)) := by
      rw [heq]
      exact hm.log.indicator (hms R)
    have hnn : 0 ≤ᵐ[μ.restrict {x | R ≤ Zᶜ.indicator r x}] fun x => Real.log (Zᶜ.indicator r x) :=
      ae_restrict_of_forall_mem (hms R) fun x hx => Real.log_nonneg (hR1.trans hx)
    have hio : IntegrableOn (fun x => Real.log (Zᶜ.indicator r x)) {x | R ≤ Zᶜ.indicator r x} μ :=
      ⟨hm.log.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal hnn).2 (hs.trans_lt ENNReal.ofReal_lt_top)⟩
    have hig : Integrable (cut Z {x | R ≤ r x} fun x => Real.log (r x)) μ := by
      rw [heq]
      exact (integrable_indicator_iff (hms R)).2 hio
    refine ⟨(hμ _ hmg (hcut0 _ _)).1.2 hig, ?_⟩
    rw [(hμ _ hmg (hcut0 _ _)).2 hig, heq, integral_indicator (hms R)]
    rw [← ofReal_integral_eq_lintegral_ofReal hio hnn] at hs
    have h0 : 0 ≤ max C 0 := le_max_right _ _
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hs
  refine ⟨huniv _ ▸ (hlog _ le_rfl).1, h2.trans (le_max_left _ _), fun R hR => (hlog R hR).2.trans ?_⟩
  have hR0 : 0 < R := (Real.exp_pos 1).trans_le hR
  have hl : 0 ≤ Real.log R := Real.log_nonneg ((Real.one_le_exp zero_le_one).trans hR)
  gcongr
  exact le_max_right _ _

end GlobalTheory.Mean4O.LogTail
