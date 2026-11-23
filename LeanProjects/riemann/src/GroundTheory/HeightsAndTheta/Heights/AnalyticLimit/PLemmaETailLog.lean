import Mathlib
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StLemmaETailLog
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StLemmaETailMass
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StTailLogOfMass
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open Filter Topology
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsSection logNormSec)

variable {D : ℕ} {X : Type*} [TopologicalSpace X]

theorem continuousAt_of_chart {β : Type*} [TopologicalSpace β] (A : FinHolAtlas D X) {f : X → β}
    {U : Set X} (hU : IsOpen U) {z : X} (hz : z ∈ U) (j : Fin A.n) (hzj : z ∈ (A.chart j).source)
    (hf : ContinuousOn (f ∘ (A.chart j).symm) ((A.chart j).target ∩ (A.chart j).symm ⁻¹' U)) :
    ContinuousAt f z := by
  set c := A.chart j
  have hmem : c z ∈ c.target ∩ c.symm ⁻¹' U := ⟨c.map_source hzj, by simpa [c.left_inv hzj] using hz⟩
  have h1 : ContinuousAt (f ∘ c.symm) (c z) :=
    hf.continuousAt ((c.isOpen_inter_preimage_symm hU).mem_nhds hmem)
  have h2 : ContinuousAt (f ∘ c.symm ∘ c) z := h1.comp (c.continuousAt hzj)
  refine h2.congr ?_
  filter_upwards [c.open_source.mem_nhds hzj] with y hy
  simp [c.left_inv hy]

theorem normSec_eventuallyEq {A : FinHolAtlas D X} {L : LocPot X} {s : X → X → ℂ}
    (hs : IsSection A L s) (y : X) :
    (fun z => ‖s z z‖ * Real.exp (-L.φ z z)) =ᶠ[𝓝 y] fun z => ‖s y z‖ * Real.exp (-L.φ y z) := by
  filter_upwards [(L.isOpen_U y).mem_nhds (L.mem_U y)] with z hz
  exact hs.2 z y z ⟨L.mem_U z, hz⟩

theorem continuous_normSec {A : FinHolAtlas D X} {L : LocPot X} {s : X → X → ℂ}
    (hL : IsPotential A L) (hs : IsSection A L s) :
    Continuous fun z => ‖s z z‖ * Real.exp (-L.φ z z) := by
  refine continuous_iff_continuousAt.2 fun y => ?_
  obtain ⟨j, hj⟩ := A.cover y
  have h : ContinuousAt (fun z => ‖s y z‖ * Real.exp (-L.φ y z)) y := by
    refine continuousAt_of_chart A (L.isOpen_U y) (L.mem_U y) j hj ?_
    have h1 := (hs.1 y j).continuousOn
    have h2 := (hL.1 y j).continuousOn
    exact h1.norm.mul (Real.continuous_exp.comp_continuousOn h2.neg)
  exact h.congr (normSec_eventuallyEq hs y).symm

theorem isOpen_secOpen {A : FinHolAtlas D X} {L : LocPot X} {s : X → X → ℂ}
    (hL : IsPotential A L) (hs : IsSection A L s) : IsOpen (secOpen s) := by
  have h : secOpen s = (fun z => ‖s z z‖ * Real.exp (-L.φ z z)) ⁻¹' {0}ᶜ := by
    ext y
    simp [secOpen, Real.exp_ne_zero]
  rw [h]
  exact (continuous_normSec hL hs).isOpen_preimage _ isOpen_compl_singleton

theorem continuousOn_rSec {A : FinHolAtlas D X} {L : LocPot X} {s : X → X → ℂ}
    (hL : IsPotential A L) (hs : IsSection A L s) : ContinuousOn (rSec L s) (secOpen s) := by
  refine continuousOn_const.sub (continuousOn_const.mul
    ((continuous_normSec hL hs).continuousOn.log fun y hy => ?_))
  exact mul_ne_zero (norm_ne_zero_iff.2 hy) (Real.exp_ne_zero _)

theorem exp_one_le_rSec {L : LocPot X} {s : X → X → ℂ}
    (hle : ∀ y, ‖s y y‖ * Real.exp (-L.φ y y) ≤ 1) (y : X) : Real.exp 1 ≤ rSec L s y := by
  have h : logNormSec L s y ≤ 0 :=
    Real.log_nonpos (mul_nonneg (norm_nonneg _) (Real.exp_pos _).le) (hle y)
  unfold rSec
  linarith

theorem LemmaETailLog.proof (h₁ : LemmaETailMass.Statement) (h₂ : TailLogOfMass.Statement) :
    LemmaETailLog.Statement := by
  intro X _ _ _ D A Om L s hL hs hd hle C₁ hC₁
  obtain ⟨CE, hCE⟩ := h₁ D A Om L s hL hs hd hle C₁ hC₁
  refine ⟨shellConst D * CE, fun u hu => ?_⟩
  exact h₂ D A (secOpen s) (rSec L s) Om.pot u (isOpen_secOpen hL hs) (continuousOn_rSec hL hs)
    (fun y _ => exp_one_le_rSec hle y) Om.isPot (fun i => (hu i).smooth) (fun i => (hu i).nonneg) CE
    (hCE u hu)

end GroundTheory.Heights₂.Heights.AnalyticLimit
