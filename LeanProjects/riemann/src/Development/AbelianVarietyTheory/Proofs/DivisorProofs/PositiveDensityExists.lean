import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqOfNonneg
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.CurveDens GlobalTheory.Cartier
open scoped ComplexOrder

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CurveDens

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}

theorem transDet_trans_chart (c c' c'' : AlgChart p σ D) {y : CxPts p σ} (hy : y ∈ c.e.source)
    (hy' : y ∈ c'.e.source) (hy'' : y ∈ c''.e.source) :
    ChartGlue.transDet c.e c''.e y =
      ChartGlue.transDet c.e c'.e y * ChartGlue.transDet c'.e c''.e y := by
  have ho := ChartGlue.isOpen_over c.e (c'.e.open_source.inter c''.e.open_source)
  have hm : c.e y ∈ c.e.target ∩ c.e.symm ⁻¹' (c'.e.source ∩ c''.e.source) :=
    ChartGlue.mem_over c.e hy ⟨hy', hy''⟩
  have e : c''.e ∘ c.e.symm =ᶠ[𝓝 (c.e y)] (c''.e ∘ c'.e.symm) ∘ (c'.e ∘ c.e.symm) :=
    eventually_of_mem (ho.mem_nhds hm) fun w hw => by
      simp only [Function.comp_apply, c'.e.left_inv hw.2.1]
  have hf : DifferentiableAt ℂ (c'.e ∘ c.e.symm) (c.e y) :=
    (c.holo_trans c').differentiableAt
      ((ChartGlue.isOpen_over c.e c'.e.open_source).mem_nhds (ChartGlue.mem_over c.e hy hy'))
  have hfy : (c'.e ∘ c.e.symm) (c.e y) = c'.e y := by simp [c.e.left_inv hy]
  have hg : DifferentiableAt ℂ (c''.e ∘ c'.e.symm) ((c'.e ∘ c.e.symm) (c.e y)) := by
    rw [hfy]
    exact (c'.holo_trans c'').differentiableAt
      ((ChartGlue.isOpen_over c'.e c''.e.open_source).mem_nhds (ChartGlue.mem_over c'.e hy' hy''))
  rw [ChartGlue.transDet, e.fderiv_eq, fderiv_comp _ hg hf, hfy, ChartGlue.transDet,
    ChartGlue.transDet]
  simp only [ContinuousLinearMap.det]
  exact (LinearMap.det_comp _ _).trans (mul_comm _ _)

theorem transDet_chart_ne_zero (c c' : AlgChart p σ D) {y : CxPts p σ} (hy : y ∈ c.e.source)
    (hy' : y ∈ c'.e.source) : ChartGlue.transDet c.e c'.e y ≠ 0 := by
  intro h
  have := transDet_trans_chart c c' c hy hy' hy
  rw [c.transDet_self hy, h, zero_mul] at this
  exact one_ne_zero this

theorem continuousAt_transDet_chart (c c' : AlgChart p σ D) {y : CxPts p σ} (hy : y ∈ c.e.source)
    (hy' : y ∈ c'.e.source) : ContinuousAt (ChartGlue.transDet c.e c'.e) y := by
  have hW : y ∈ ptsIn p σ (c.U ⊓ c'.U) :=
    mem_ptsIn_inf.2 ⟨c.source_subset hy, c'.source_subset hy'⟩
  have h1 : ContinuousAt (ev p σ _ (c.isFrame.ratio c'.isFrame).val) y :=
    (continuousOn_ev _).continuousAt ((isOpen_ptsIn _).mem_nhds hW)
  refine h1.congr ?_
  filter_upwards [(c.e.open_source.inter c'.e.open_source).mem_nhds ⟨hy, hy'⟩] with z hz
  exact c.ev_ratio c' hz.1 hz.2

theorem exists_isDens_pos : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ)
    [CompactSpace (CxPts p σ)] [T2Space (CxPts p σ)] [SecondCountableTopology (CxPts p σ)],
    Nonempty (AnRead p σ 1) → ∃ w : AlgChart p σ 1 → CxPts p σ → ℝ,
      IsDens w ∧ ∀ c : AlgChart p σ 1, ∀ y ∈ c.e.source, 0 < w c y := by
  intro k _ X p σ _ _ _ ⟨R⟩
  obtain ⟨s, hs⟩ := R.exists_finite
  obtain ⟨f, hf⟩ := PartitionOfUnity.exists_isSubordinate (X := CxPts p σ) (ι := s) isClosed_univ
    (fun i => (R.chart i.1).e.source) (fun i => (R.chart i.1).e.open_source)
    (fun y _ => by
      obtain ⟨i, hi, hy⟩ := hs y
      exact Set.mem_iUnion.2 ⟨⟨i, hi⟩, hy⟩)
  have hsrc : ∀ (i : s) (y : CxPts p σ), f i y ≠ 0 → y ∈ (R.chart i.1).e.source := fun i y h =>
    hf i (subset_tsupport _ h)
  refine ⟨fun c y => ∑ i : s, f i y * ‖ChartGlue.transDet c.e (R.chart i.1).e y‖ ^ 2,
    ⟨fun c c' y hy hy' => ?_, fun c => ?_⟩, fun c y hy => ?_⟩
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : f i y = 0
    · simp [h]
    · rw [transDet_trans_chart c c' _ hy hy' (hsrc i y h), norm_mul, mul_pow]
      ring
  · refine continuousOn_finset_sum _ fun i _ => ?_
    have hg : ContinuousOn (fun y => f i y * ‖ChartGlue.transDet c.e (R.chart i.1).e y‖ ^ 2)
        c.e.source := fun y hy => by
      refine ContinuousAt.continuousWithinAt ?_
      by_cases h : y ∈ tsupport (f i)
      · exact (f i).continuous.continuousAt.mul
          ((continuousAt_transDet_chart c _ hy (hf i h)).norm.pow 2)
      · refine (continuousAt_const (y := (0 : ℝ))).congr ?_
        filter_upwards [notMem_tsupport_iff_eventuallyEq.1 h] with z hz
        rw [hz, Pi.zero_apply, zero_mul]
    exact hg.comp c.e.continuousOn_symm fun v hv => c.e.map_target hv
  · obtain ⟨i, hi⟩ := f.exists_pos (Set.mem_univ y)
    refine Finset.sum_pos' (fun j _ => mul_nonneg (f.nonneg j y) (sq_nonneg _))
      ⟨i, Finset.mem_univ _, mul_pos hi (pow_pos (norm_pos_iff.2 ?_) 2)⟩
    exact transDet_chart_ne_zero c _ hy (hsrc i y hi.ne')

end GlobalTheory.CurveDens
