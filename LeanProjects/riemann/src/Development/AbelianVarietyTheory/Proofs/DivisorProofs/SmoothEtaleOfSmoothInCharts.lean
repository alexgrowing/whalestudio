import Mathlib
import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.EtaleEmpty

namespace GlobalTheory.OTY

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

section

variable {n : ℕ} {Y : Type} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι La : Type} [AddCommGroup La]

theorem etaleSmooth_contDiffAt_chart {A : WeightedAtlas n Y ι La} {U : Set Y} {z : Y → V n}
    (hE : Etale A U z) {x : Y} (hx : x ∈ U) {i : ι} (hi : x ∈ (A.chart i).source) :
    ContDiffAt ℂ ∞ (z ∘ (A.chart i).symm) (A.chart i x) := by
  have ho : IsOpen ((A.chart i).target ∩ (A.chart i).symm ⁻¹' U) :=
    (A.chart i).isOpen_inter_preimage_symm hE.isOpen
  have hm : A.chart i x ∈ (A.chart i).target ∩ (A.chart i).symm ⁻¹' U :=
    ⟨(A.chart i).map_source hi, by simp [(A.chart i).left_inv hi, hx]⟩
  have hk : ∀ k, ContDiffOn ℂ ∞ (fun v => (z ∘ (A.chart i).symm) v k)
      ((A.chart i).target ∩ (A.chart i).symm ⁻¹' U) := fun k =>
    contDiffOn_of_differentiableOn n _ _ ho
      ((EuclideanSpace.proj k : V n →L[ℂ] ℂ).differentiable.comp_differentiableOn (hE.holo i))
  have hpi := contDiffOn_pi.mpr hk
  have h2 : ContDiffOn ℂ ∞ (z ∘ (A.chart i).symm)
      ((A.chart i).target ∩ (A.chart i).symm ⁻¹' U) :=
    (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => ℂ)).symm.contDiff.comp_contDiffOn hpi
  exact (h2 _ hm).contDiffAt (ho.mem_nhds hm)

theorem etaleSmooth_inverse {A : WeightedAtlas n Y ι La} {U : Set Y} {z : Y → V n}
    (hE : Etale A U z) (e : OpenPartialHomeomorph U (V n))
    (he : IsChart n (fun y : U => z y) e) (v : V n) (hv : v ∈ e.target) (i : ι)
    (hi : ((e.symm v : U) : Y) ∈ (A.chart i).source) :
    ContDiffAt ℂ ∞ (fun v' => A.chart i (e.symm v' : Y)) v ∧
      (∀ᶠ v' in 𝓝 v, ((e.symm v' : U) : Y) ∈ (A.chart i).source) := by
  have hzs : ∀ v' ∈ e.target, z (e.symm v' : Y) = v' := fun v' hv' => by
    have := he (e.map_target hv')
    simp only at this
    rw [this, e.right_inv hv']
  set x : U := e.symm v with hxdef
  set G : V n → V n := fun v' => A.chart i (e.symm v' : Y) with hG
  have hz := etaleSmooth_contDiffAt_chart hE x.2 hi
  have hdet : (GlobalTheory.OTY.jz A z i x).det ≠ 0 := hE.det_ne i x x.2 hi
  set f' := (GlobalTheory.OTY.jz A z i x).toContinuousLinearEquivOfDetNeZero hdet with hf'def
  have hf' : HasFDerivAt (z ∘ (A.chart i).symm) (f' : V n →L[ℂ] V n) (A.chart i x) := by
    rw [hf'def, ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero]
    exact (hz.differentiableAt (by simp)).hasFDerivAt
  have hn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  have hstrict := hz.hasStrictFDerivAt' hf' hn
  have hzx : (z ∘ (A.chart i).symm) (A.chart i x) = v := by
    rw [Function.comp_apply, (A.chart i).left_inv hi]
    exact hzs v hv
  have hGv : G v = A.chart i x := rfl
  have hc0 : ContinuousAt (Subtype.val ∘ e.symm) v :=
    continuous_subtype_val.continuousAt.comp (e.continuousAt_symm hv)
  have hsrc : ∀ᶠ v' in 𝓝 v, ((e.symm v' : U) : Y) ∈ (A.chart i).source :=
    hc0.eventually_mem ((A.chart i).open_source.mem_nhds hi)
  have hGc : ContinuousAt G v :=
    ContinuousAt.comp (f := Subtype.val ∘ e.symm) ((A.chart i).continuousAt hi) hc0
  have hright : ∀ᶠ v' in 𝓝 v, (z ∘ (A.chart i).symm) (G v') = v' := by
    filter_upwards [hsrc, e.open_target.mem_nhds hv] with v' h1 h2
    rw [hG]
    simp only [Function.comp_apply]
    rw [(A.chart i).left_inv h1]
    exact hzs v' h2
  have hleft : ∀ᶠ v' in 𝓝 v,
      hstrict.localInverse _ _ _ ((z ∘ (A.chart i).symm) (G v')) = G v' := by
    have := hGc.tendsto.eventually (f := G) (by rw [hGv]; exact hstrict.eventually_left_inverse)
    exact this
  have heq : G =ᶠ[𝓝 v] hstrict.localInverse _ _ _ := by
    filter_upwards [hleft, hright] with v' h1 h2
    rw [← h1, h2]
  have hloc : ContDiffAt ℂ ∞ (hz.localInverse hf' hn) ((z ∘ (A.chart i).symm) (A.chart i x)) :=
    hz.to_localInverse hf' hn
  rw [hzx] at hloc
  exact ⟨hloc.congr_of_eventuallyEq heq, hsrc⟩

theorem etaleSmooth_complex {A : WeightedAtlas n Y ι La} {U : Set Y} {z : Y → V n}
    (hE : Etale A U z) (u : Y → ℂ)
    (hu : ∀ x ∈ U, ∃ i, x ∈ (A.chart i).source ∧
      ContDiffAt ℝ ∞ (u ∘ (A.chart i).symm) (A.chart i x)) :
    Smooth n (fun y : U => z y) (fun y : U => u y) := by
  intro e he v hv
  obtain ⟨i, hi, hui⟩ := hu _ (e.symm v).2
  obtain ⟨hG, hsrc⟩ := etaleSmooth_inverse hE e he v hv i hi
  have hc : ContDiffAt ℝ ∞ ((u ∘ (A.chart i).symm) ∘ fun v' => A.chart i (e.symm v' : Y)) v :=
    hui.comp v (hG.restrict_scalars ℝ)
  refine (hc.congr_of_eventuallyEq ?_).contDiffWithinAt
  filter_upwards [hsrc] with v' h1
  simp [(A.chart i).left_inv h1]

end

theorem smooth_etale_of_smooth_in_charts : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (U : Set Y) (z : Y → V n), Etale A U z → (∀ u : Y → ℂ, (∀ x ∈ U, ∃ i, x ∈ (A.chart i).source ∧ ContDiffAt ℝ ∞ (u ∘ (A.chart i).symm) (A.chart i x)) → Smooth n (fun y : U => z y) (fun y : U => u y)) ∧ (∀ φ : Y → ℝ, (∀ x ∈ U, ∃ i, x ∈ (A.chart i).source ∧ ContDiffAt ℝ ∞ (φ ∘ (A.chart i).symm) (A.chart i x)) → SmoothR n (fun y : U => z y) (fun y : U => φ y)) := by
  intro n Y _ _ _ _ _ ι La _ A U z hE
  refine ⟨fun u hu => etaleSmooth_complex hE u hu, fun φ hφ => ?_⟩
  refine etaleSmooth_complex hE (fun y => (φ y : ℂ)) fun x hx => ?_
  obtain ⟨i, hi, h⟩ := hφ x hx
  exact ⟨i, hi, Complex.ofRealCLM.contDiff.contDiffAt.comp _ h⟩

end GlobalTheory.OTY
