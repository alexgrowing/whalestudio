import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnalyticLogResolution
import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffAtOfIsPotential
open MeasureTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions GlobalTheory.LogResInt
open scoped ENNReal ContDiff Topology

namespace GlobalTheory.BoundarySmooth

variable {d : ℕ} {X : Type} [TopologicalSpace X]

theorem sec_continuousAt (A : FinHolAtlas d X) (L : LocPot X) (s : X → X → ℂ)
    (hs : IsSection A L s) (y0 : X) : ContinuousAt (s y0) y0 := by
  obtain ⟨j, hj⟩ := A.cover y0
  have h1 : AnalyticAt ℂ (s y0 ∘ (A.chart j).symm) (A.chart j y0) := by
    refine hs.1 y0 j _ ⟨(A.chart j).map_source hj, ?_⟩
    simp only [Set.mem_preimage, (A.chart j).left_inv hj]
    exact L.mem_U y0
  have h2 : ContinuousAt ((s y0 ∘ (A.chart j).symm) ∘ A.chart j) y0 :=
    ContinuousAt.comp (f := A.chart j) h1.continuousAt ((A.chart j).continuousAt hj)
  refine h2.congr ?_
  filter_upwards [(A.chart j).open_source.mem_nhds hj] with y hy
  simp [Function.comp_apply, (A.chart j).left_inv hy]

theorem sec_eventually_ne (A : FinHolAtlas d X) (L : LocPot X) (s : X → X → ℂ)
    (hs : IsSection A L s) (y0 : X) (h0 : s y0 y0 ≠ 0) : ∀ᶠ z in 𝓝 y0, s z z ≠ 0 := by
  filter_upwards [(sec_continuousAt A L s hs y0).eventually_ne h0,
    (L.isOpen_U y0).mem_nhds (L.mem_U y0)] with z hz hzU
  intro hzz
  have := hs.2 z y0 z ⟨L.mem_U z, hzU⟩
  rw [hzz, norm_zero, zero_mul] at this
  have hpos : 0 < ‖s y0 z‖ * Real.exp (-L.φ y0 z) :=
    mul_pos (norm_pos_iff.mpr hz) (Real.exp_pos _)
  linarith

theorem logNormSec_contDiffAt (A : FinHolAtlas d X) (L : LocPot X) (s : X → X → ℂ)
    (hL : IsPotential A L) (hs : IsSection A L s) (j : Fin A.n) (y : Fin d → ℂ)
    (hy : y ∈ (A.chart j).target) (hne : s ((A.chart j).symm y) ((A.chart j).symm y) ≠ 0) :
    ContDiffAt ℝ ∞ (fun w => logNormSec L s ((A.chart j).symm w)) y := by
  set y0 := (A.chart j).symm y with hy0def
  have hyU : y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' L.U y0 := ⟨hy, L.mem_U y0⟩
  have hopen : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' L.U y0) :=
    (A.chart j).isOpen_inter_preimage_symm (L.isOpen_U y0)
  have hΦ : ContDiffAt ℝ ∞ (L.φ y0 ∘ (A.chart j).symm) y :=
    (hL.1 y0 j).contDiffAt (hopen.mem_nhds hyU)
  have hS : ContDiffAt ℝ ∞ (s y0 ∘ (A.chart j).symm) y :=
    ((hs.1 y0 j y hyU).contDiffAt (n := ∞)).restrict_scalars ℝ
  have hSz : (s y0 ∘ (A.chart j).symm) y ≠ 0 := hne
  have hG : ContDiffAt ℝ ∞ (fun w => Real.log
      (‖(s y0 ∘ (A.chart j).symm) w‖ * Real.exp (-((L.φ y0 ∘ (A.chart j).symm) w)))) y := by
    refine ContDiffAt.log ((hS.norm ℝ hSz).mul hΦ.neg.exp) ?_
    have : 0 < ‖(s y0 ∘ (A.chart j).symm) y‖ := norm_pos_iff.mpr hSz
    positivity
  refine hG.congr_of_eventuallyEq ?_
  filter_upwards [hopen.mem_nhds hyU] with w hw
  have hg := hs.2 ((A.chart j).symm w) y0 ((A.chart j).symm w) ⟨L.mem_U _, hw.2⟩
  simp only [Function.comp_apply, logNormSec]
  rw [hg]

theorem boundary_isClosed_and_smoothOn :
    ∀ (d : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas d X) (m : ℕ)
    (Λ : Fin m → LocPot X) (σ : Fin m → X → X → ℂ) (c : ℝ),
    (∀ i, IsPotential A (Λ i) ∧ IsSection A (Λ i) (σ i) ∧ ∀ y, normSec (Λ i) (σ i) y ≤ 1) →
    IsClosed (boundary σ) ∧ A.SmoothOn (boundary σ)ᶜ (fun y => pFun Λ σ c y / 2) := by
  intro d X _ A m Λ σ c h
  have hcl : IsClosed (boundary σ) := by
    refine isOpen_compl_iff.mp (isOpen_iff_mem_nhds.mpr fun y0 hy0 => ?_)
    have hy0' : ∀ i, σ i y0 y0 ≠ 0 := fun i hi => hy0 ⟨i, hi⟩
    have hev : ∀ᶠ z in 𝓝 y0, ∀ i, σ i z z ≠ 0 :=
      Filter.eventually_all.mpr fun i => sec_eventually_ne A (Λ i) (σ i) (h i).2.1 y0 (hy0' i)
    filter_upwards [hev] with z hz
    rintro ⟨i, hi⟩
    exact hz i hi
  refine ⟨hcl, fun j => ?_⟩
  intro y hy
  apply ContDiffAt.contDiffWithinAt
  have hne : ∀ i, σ i ((A.chart j).symm y) ((A.chart j).symm y) ≠ 0 :=
    fun i hi => hy.2 ⟨i, hi⟩
  have hr : ∀ i, ContDiffAt ℝ ∞
      (fun w => Real.log (rFun (Λ i) (σ i) ((A.chart j).symm w))) y := by
    intro i
    have hl := logNormSec_contDiffAt A (Λ i) (σ i) (h i).1 (h i).2.1 j y hy.1 (hne i)
    refine ContDiffAt.log (contDiffAt_const.sub (contDiffAt_const.mul hl)) ?_
    have hle : logNormSec (Λ i) (σ i) ((A.chart j).symm y) ≤ 0 := by
      unfold logNormSec
      exact Real.log_nonpos (by positivity) ((h i).2.2 _)
    have := Real.exp_pos 1
    simp only [rFun]
    linarith
  have hsum : ContDiffAt ℝ ∞
      (fun w => ∑ i, Real.log (rFun (Λ i) (σ i) ((A.chart j).symm w))) y :=
    ContDiffAt.sum fun i _ => hr i
  have := (contDiffAt_const (c := -c)).mul hsum |>.div_const 2
  simpa [Function.comp_def, pFun] using this

end GlobalTheory.BoundarySmooth
