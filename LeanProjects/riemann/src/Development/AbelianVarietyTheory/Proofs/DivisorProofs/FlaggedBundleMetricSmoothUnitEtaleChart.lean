import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsMetricFrOfIsMetricOn
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ChernDegreeComplex
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedFrameEventuallyFrameNearComplexPointStatement
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

namespace GlobalTheory.ChernCalc

theorem isMetricFr_smoothUnitAt : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (ι : Type) [Finite ι] (m k : ι → ℕ) (E : Fr (ratOf X) m k) (H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ), IsMetricFr E H → ∀ (y : CxPts X.str σ), ∀ A ∈ E.S (under y), ∀ τ, SmoothUnitAt (atlas X σ) (fun z => H A z τ) y ∧ ∀ c : AlgChart X.str σ X.dim, y ∈ c.e.source → ∀ᶠ v in 𝓝 (c.e y), MContDiffAt ∞ (fun u => H A (c.e.symm u) τ) v ∧ (H A (c.e.symm v) τ).PosDef := by
  intro F _ σ X ι _ m k E H hH y A hA τ
  set U : Set (CxPts X.str σ) := interior {z : CxPts X.str σ | A ∈ E.S (under z)} with hU
  have hyU : y ∈ U := mem_interior_iff_mem_nhds.2 (GlobalTheory.T.adaptedFrame_eventually_frame_near_complex_point F σ X ι m k E y A hA)
  have hUo : IsOpen U := isOpen_interior
  have hUS : ∀ z ∈ U, A ∈ E.S (under z) := fun z hz => interior_subset (s := {z : CxPts X.str σ | A ∈ E.S (under z)}) hz
  have key : ∀ c : AlgChart X.str σ X.dim, y ∈ c.e.source → ∀ᶠ v in 𝓝 (c.e y),
      MContDiffAt ∞ (fun u => H A (c.e.symm u) τ) v ∧ (H A (c.e.symm v) τ).PosDef := by
    intro c hc
    have ho : IsOpen (c.e.target ∩ c.e.symm ⁻¹' U) := c.e.isOpen_inter_preimage_symm hUo
    have hm : c.e y ∈ c.e.target ∩ c.e.symm ⁻¹' U :=
      ⟨c.e.map_source hc, by simpa [Set.mem_preimage, c.e.left_inv hc] using hyU⟩
    filter_upwards [ho.mem_nhds hm] with v hv
    refine ⟨fun i j => ?_, hH.posDef _ A (hUS _ hv.2) τ⟩
    have hre := contDiffOn_chart (S := U) (f := fun z => (H A z τ i j).re)
      (fun z hz => (hH.smooth z A (hUS z hz) τ i j).1) c
    have him := contDiffOn_chart (S := U) (f := fun z => (H A z τ i j).im)
      (fun z hz => (hH.smooth z A (hUS z hz) τ i j).2) c
    have h1 := (hre.contDiffAt (ho.mem_nhds hv))
    have h2 := (him.contDiffAt (ho.mem_nhds hv))
    have h3 : ContDiffAt ℝ ∞ (fun u => ((((H A (c.e.symm u) τ i j).re : ℝ) : ℂ) +
        (((H A (c.e.symm u) τ i j).im : ℝ) : ℂ) * Complex.I)) v :=
      (Complex.ofRealCLM.contDiff.contDiffAt.comp v h1).add
        ((Complex.ofRealCLM.contDiff.contDiffAt.comp v h2).mul contDiffAt_const)
    refine h3.congr_of_eventuallyEq (Eventually.of_forall fun u => ?_)
    simp [Complex.re_add_im]
  refine ⟨⟨?_, fun c hc => (key c hc).mono fun v hv => hv.1⟩, key⟩
  exact (Matrix.isUnit_iff_isUnit_det _).1 (hH.posDef y A hA τ).isUnit

end GlobalTheory.ChernCalc
