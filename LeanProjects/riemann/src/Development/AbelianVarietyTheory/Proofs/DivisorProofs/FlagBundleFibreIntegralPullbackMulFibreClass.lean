import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsMetricFrOfIsMetricOn
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ChernDegreeComplex
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothFormsCalculusHolomorphicAtlas
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VarietyComplexPointsMapIsHolomorphicStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullFlagGradedLineChernFormsSmoothDbarClosedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFlaggedBundleMetricPullGramRefinementStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedFrameEventuallyFrameNearComplexPointStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.BsLApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnivEqOfLocalPreimageEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousOnDens
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ChernCalc

theorem fibre_integral : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X Y : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X) (hf : f ≫ X.str = Y.str), Refines E E' φ f → ∀ H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ, IsMetricOn E ⊤ H → ∀ α : (atlas X σ).Fld, (atlas X σ).IsForm α → (atlas Y σ).integral ((atlas X σ).pullback (atlas Y σ) (ptMap σ f hf) α * evalF (atlas Y σ) (grF E' (pullGram E H φ f hf)) (fibrePoint m)) = (atlas X σ).integral α := by
  intro F _ σ X Y ι _ m E E' φ f hf hR H hH α hα
  have hol := GlobalTheory.T.varietyComplexPointsMap_isHolomorphic F σ X Y f hf
  have hmet := GlobalTheory.T.isFlaggedBundleMetric_pullGram_refinement F σ X Y ι m E E' φ f hf hR H hH
  have hgr := GlobalTheory.T.fullFlagGradedLineChernForms_smooth_dbarClosed F σ Y ι m E' _ hmet
  have hpb := (((GlobalTheory.formCalculus _ _ (atlas X σ)).2.2.2.2 _ _ (atlas Y σ) _ hol).2 1 α α).2.2.2 hα
  have hev := ((GlobalTheory.formCalculus _ _ (atlas Y σ)).2.2.2.1 (Root m) (grF E' (pullGram E H φ f hf)) (fibrePoint m)
    fun x => (hgr x).1).1
  have hβ := (((GlobalTheory.formCalculus _ _ (atlas Y σ)).2.1 1 _ _ hpb.1 hev)).2.1
  have key : ∀ s : ℤˣ, (atlas Y σ).part ((atlas X σ).pullback (atlas Y σ) (ptMap σ f hf) α *
      evalF (atlas Y σ) (grF E' (pullGram E H φ f hf)) (fibrePoint m)) s Set.univ = (atlas X σ).part α s Set.univ := by
    intro s
    refine GlobalTheory.FlagCell2.univ_eq_of_local_preimage_eq _ _ (ptMap σ f hf) hol.1.measurable _ _ fun x => ?_
    have := X.smooth_str
    obtain ⟨c, hc⟩ := AlgChart.exists_mem_source (D := X.dim) (σ := σ) x
    obtain ⟨A, hA⟩ := E.nonempty (under x)
    refine ⟨c.e.source ∩ interior {z | A ∈ E.S (under z)}, c.e.open_source.inter isOpen_interior,
      ⟨hc, mem_interior_iff_mem_nhds.2 (GlobalTheory.T.adaptedFrame_eventually_frame_near_complex_point F σ X ι m 0 E x A hA)⟩, fun T hT hTU => ?_⟩
    exact GlobalTheory.FlagCell2.LocFib.part_preimage F σ X Y ι m E E' φ f hf hR H hH α hα hβ s c A _ (c.e.open_source.inter isOpen_interior)
      Set.inter_subset_left (fun z hz => (interior_subset (s := {z | A ∈ E.S (under z)}) hz.2 :)) T hT hTU
  rw [HolAtlas.integral, HolAtlas.integral, measureReal_def, measureReal_def, measureReal_def, measureReal_def, key, key]

end GlobalTheory.ChernCalc
