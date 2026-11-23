import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.EtaleEmpty
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory

theorem smooth_cutoff_mul_sec : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (la : La) (W : Set Y) (χ : Y → ℝ) (h : ι → Y → ℂ), IsOpen W → A.SmoothFn χ → tsupport χ ⊆ W → A.IsSecOn la W h → A.IsSSec la (fun i y => (χ y : ℂ) * h i y) := by
  intro n Y _ _ _ _ _ ι La _ A la W χ h hW hχ hsupp hh
  have hzero : ∀ y, y ∉ W → χ y = 0 := fun y hy =>
    Function.notMem_support.1 (fun hs => hy (hsupp (subset_tsupport χ hs)))
  refine ⟨fun i => ?_, fun i j y hi hj => ?_⟩
  · intro v hv
    refine ContDiffAt.contDiffWithinAt ?_
    set e := A.chart i
    have hvn : e.target ∈ 𝓝 v := e.open_target.mem_nhds hv
    have hχv : ContDiffAt ℝ ∞ (fun v => ((χ (e.symm v) : ℝ) : ℂ)) v :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp v ((hχ i).contDiffAt hvn)
    by_cases hy : e.symm v ∈ W
    · have hU : IsOpen (e.target ∩ e.symm ⁻¹' W) := e.isOpen_inter_preimage_symm hW
      have hh' : ContDiffAt ℝ ∞ (h i ∘ e.symm) v :=
        hyq_contDiffAt_of_holo hU (hh.1 i) ⟨hv, hy⟩
      exact hχv.mul hh'
    · have hnt : e.symm v ∉ tsupport χ := fun ht => hy (hsupp ht)
      have hev : χ =ᶠ[𝓝 (e.symm v)] 0 := notMem_tsupport_iff_eventuallyEq.1 hnt
      have hev' : ∀ᶠ v' in 𝓝 v, χ (e.symm v') = 0 := (e.continuousAt_symm hv).eventually hev
      refine (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_
      filter_upwards [hev'] with v' hv'
      simp [hv']
  · by_cases hy : y ∈ W
    · show (χ y : ℂ) * h i y = A.g la i j y * ((χ y : ℂ) * h j y)
      rw [hh.2 i j y hy hi hj]; ring
    · show (χ y : ℂ) * h i y = A.g la i j y * ((χ y : ℂ) * h j y)
      simp [hzero y hy]

end GlobalTheory
