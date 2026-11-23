import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.AntisymmFibrePointTwo
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopChernDensityInvariantHolomorphicFrameChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernTopChartIndependent
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHolomorphicInvertibleFrameCoordinates
open AlgebraicGeometry MvPolynomial GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
open Filter Topology
open scoped Matrix
open scoped ComplexOrder

namespace GlobalTheory.GoodMetric

variable {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {ι : Type} {m : ι → ℕ} {E : Fr (ratOf X) m 0}
  {O : X.X.Opens} {H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ}

theorem IsMetricOn.mContDiffAt_chart (hM : IsMetricOn E O H) {y : CxPts X.str σ} (hy : y ∈ ptsIn X.str σ O)
    (c : AlgChart X.str σ X.dim) (hc : y ∈ c.e.source) {A : Mat m X.Fn} (hA : A ∈ E.S (under y)) (τ : ι) :
    MContDiffAt 2 (fun u => H A (c.e.symm u) τ) (c.e y) := by
  intro a b
  have hy'' : c.e.symm (c.e y) = y := c.e.left_inv hc
  have hsm := hM.smooth y hy A hA
  have hre := GlobalTheory.ChernWeilLine.cInfAt_eventually (hsm τ a b).1
  have him := GlobalTheory.ChernWeilLine.cInfAt_eventually (hsm τ a b).2
  have hn : ∀ {f : CxPts X.str σ → ℝ}, (∀ᶠ z in 𝓝 y, CInfAt f z) → ContDiffAt ℝ 2 (f ∘ c.e.symm) (c.e y) := by
    intro f hf
    have hs : c.e.target ∩ c.e.symm ⁻¹' {z | CInfAt f z} ∈ 𝓝 (c.e y) := by
      refine Filter.inter_mem (c.e.open_target.mem_nhds (c.e.map_source hc)) ?_
      exact (c.e.continuousAt_symm (c.e.map_source hc)).preimage_mem_nhds (hy''.symm ▸ hf)
    exact ((contDiffOn_chart (fun z hz => hz) c).contDiffAt hs).of_le (by norm_cast)
  have h1 := (Complex.ofRealCLM.contDiff.contDiffAt.comp _ (hn hre)).add
    ((Complex.ofRealCLM.contDiff.contDiffAt.comp _ (hn him)).mul (contDiffAt_const (c := Complex.I)))
  refine h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun u => ?_)
  simp only [Function.comp_apply, Complex.ofRealCLM_apply]
  exact (Complex.re_add_im _).symm

theorem IsMetricOn.isUnit_det_chart (hM : IsMetricOn E O H) {y : CxPts X.str σ} (hy : y ∈ ptsIn X.str σ O)
    (c : AlgChart X.str σ X.dim) (hc : y ∈ c.e.source) {A : Mat m X.Fn} (hA : A ∈ E.S (under y)) (τ : ι) :
    IsUnit (H A (c.e.symm (c.e y)) τ).det := by
  rw [c.e.left_inv hc]
  exact (Matrix.isUnit_iff_isUnit_det _).1 (hM.posDef y hy A hA τ).isUnit

theorem IsMetricOn.chernTop_frame [Finite ι] (hM : IsMetricOn E O H) (R : MvPolynomial (ι × ℕ) ℝ) {y : CxPts X.str σ}
    (hy : y ∈ ptsIn X.str σ O) (c : AlgChart X.str σ X.dim) (hc : y ∈ c.e.source) {A A' : Mat m X.Fn}
    (hA : A ∈ E.S (under y)) (hA' : A' ∈ E.S (under y)) :
    chernTop R (fun v => H A (c.e.symm v)) (c.e y) = chernTop R (fun v => H A' (c.e.symm v)) (c.e y) := by
  have hP : Par 0 ((ratOf X).O (under y)).toSubring (A * A'⁻¹) := (Fr.mem_iff hA').1 hA
  refine GlobalTheory.PointChern.chernTop_changeFrame R _ _ (fun w => (A * A'⁻¹).map (ratVal · (c.e.symm w))) (fun _ => 1) _
    (fun _ => one_pos) (fun τ i j => GlobalTheory.FrameLift.analyticAt_ratVal c hc (mem_O_ratOf.1 ((hP τ).1 i j)))
    (fun τ => ?_) (hM.mContDiffAt_chart hy c hc hA') (hM.isUnit_det_chart hy c hc hA') ?_
  · obtain ⟨ψ, hψ⟩ := exists_ratVal_hom y
    simp only [c.e.left_inv hc]
    exact ((hP.map_of (ratVal · y) ψ hψ).det_ne τ).isUnit
  · have hO : ∀ᶠ z in 𝓝 y, z ∈ ptsIn X.str σ O := (isOpen_ptsIn O).mem_nhds hy
    filter_upwards [(c.e.tendsto_symm hc).eventually
      (hO.and ((GlobalTheory.FrameLift.eventually_mem hA).and (GlobalTheory.FrameLift.eventually_mem hA')))] with w hw τ
    rw [Complex.ofReal_one, one_smul]
    exact hM.trans _ hw.1 A' hw.2.2 A hw.2.1 τ

theorem IsMetricOn.chernTop_chart (hM : IsMetricOn E O H) (R : MvPolynomial (ι × ℕ) ℝ) {y : CxPts X.str σ}
    (hy : y ∈ ptsIn X.str σ O) (c c' : AlgChart X.str σ X.dim) (hc : y ∈ c.e.source) (hc' : y ∈ c'.e.source)
    {A : Mat m X.Fn} (hA : A ∈ E.S (under y)) :
    chernTop R (fun v => H A (c.e.symm v)) (c.e y) =
      ‖transDet c.e c'.e y‖ ^ 2 * chernTop R (fun v => H A (c'.e.symm v)) (c'.e y) := by
  let K : V X.dim → Mat m ℂ := fun v => H A (c'.e.symm v)
  have ho := isOpen_over c.e c'.e.open_source
  have hm := mem_over c.e hc hc'
  have hφ : AnalyticAt ℂ (c'.e ∘ c.e.symm) (c.e y) :=
    GlobalTheory.SCV.analyticAt_of_differentiableOn (c.holo_trans c') (ho.mem_nhds hm)
  have e₂ : (c'.e ∘ c.e.symm) (c.e y) = c'.e y := congrArg c'.e (c.e.left_inv hc)
  have hK2 : ∀ τ, MContDiffAt 2 (fun u => K u τ) (c'.e y) := hM.mContDiffAt_chart hy c' hc' hA
  have hKu : ∀ τ, IsUnit (K (c'.e y) τ).det := hM.isUnit_det_chart hy c' hc' hA
  have key := GlobalTheory.ChernPull.chernTop_comp R K (c'.e ∘ c.e.symm) (c.e y) hφ (e₂ ▸ hK2) (e₂ ▸ hKu)
  have hg : (fun v => H A (c.e.symm v)) =ᶠ[𝓝 (c.e y)] fun w => K ((c'.e ∘ c.e.symm) w) := by
    filter_upwards [ho.mem_nhds hm] with w hw
    simp only [K, Function.comp_apply, c'.e.left_inv hw.2]
  rw [GlobalTheory.ChernWeilLine.chernTop_congr R hg, key, e₂, transDet, Complex.sq_norm]

end GlobalTheory.GoodMetric

theorem GlobalTheory.GoodMetric.chernTop_frame_chart_trans : ∀ {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {ι : Type} [Finite ι] {m : ι → ℕ} (E : Fr (ratOf X) m 0) (O : X.X.Opens) (H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ), IsMetricOn E O H → ∀ (R : MvPolynomial (ι × ℕ) ℝ) {y : CxPts X.str σ}, y ∈ ptsIn X.str σ O → ∀ (c c' : AlgChart X.str σ X.dim), y ∈ c.e.source → y ∈ c'.e.source → ∀ {A A' : Mat m X.Fn}, A ∈ E.S (under y) → A' ∈ E.S (under y) → chernTop R (fun v => H A (c.e.symm v)) (c.e y) = ‖transDet c.e c'.e y‖ ^ 2 * chernTop R (fun v => H A' (c'.e.symm v)) (c'.e y) := by
  intro F _ σ X ι _ m E O H hM R y hy c c' hc hc' A A' hA hA'
  rw [hM.chernTop_frame R hy c hc hA hA', hM.chernTop_chart R hy c c' hc hc' hA']
