import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsMetricFrOfIsMetricOn
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ChernDegreeComplex
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedFrameEventuallyFrameNearComplexPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CurvaturePowerPullbackHolomorphicStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernTransgressionFormsFrameInvariantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlaggedBundleMetricSmoothUnitEtaleChartStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VarietyComplexPointsMapIsHolomorphicStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PulledBackGramMatricesIndependentOfFrameStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHolomorphicUnitMatrixAtRationalMatrixValuesStatement
import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.HoloSmooth

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

namespace GlobalTheory.ChernCalc

theorem contDiffOn_holoMap {n d : ℕ} {U : Set (V n)} (hU : IsOpen U) {p : V n → V d}
    (hp : DifferentiableOn ℂ p U) : ContDiffOn ℂ ∞ p U := by
  rw [contDiffOn_piLp]
  intro i
  exact ReciprocityTheory.L2DbarEstimates.contDiffOn_of_differentiableOn n _ U hU
    ((EuclideanSpace.proj i : V d →L[ℂ] ℂ).differentiable.comp_differentiableOn hp)

theorem pull_chern_of_eventually {M M' : Type} [TopologicalSpace M] [TopologicalSpace M'] {n n' : ℕ} (A : HolAtlas M n)
    (A' : HolAtlas M' n') {r : Type} [Fintype r] [DecidableEq r] {f : M' → M} (hf : A.IsHolo A' f) (G : M → Matrix r r ℂ)
    (G' T : M' → Matrix r r ℂ) (p : A'.Pt) (c : A.ι) (hc : f p.pt ∈ (A.e c).source) (hG : SmoothUnitAt A G (f p.pt))
    (hT : HolUnitAt A' T p.pt) (h : ∀ᶠ z in 𝓝 p.pt, G' z = T z * G (f z) * (T z)ᴴ) (j : ℕ) :
    pull (fderiv ℂ (A.e c ∘ f ∘ p.ch.symm) p.crd) (A.chern G j ⟨(c, f p.pt), hc⟩ : Alt n) = (A'.chern G' j p : Alt n') := by
  have hp : p.pt ∈ p.ch.source := p.2
  have hinv : p.ch.symm p.crd = p.pt := p.ch.left_inv hp
  have hU : IsOpen (p.ch.target ∩ p.ch.symm ⁻¹' (f ⁻¹' (A.e c).source)) :=
    p.ch.isOpen_inter_preimage_symm ((A.e c).open_source.preimage hf.1)
  have hmem : p.crd ∈ p.ch.target ∩ p.ch.symm ⁻¹' (f ⁻¹' (A.e c).source) :=
    ⟨p.ch.map_source hp, by rw [Set.mem_preimage, hinv]; exact hc⟩
  set ψ : V n' → V n := A.e c ∘ f ∘ p.ch.symm with hψ
  have hs : ContDiffAt ℂ ∞ ψ p.crd := (contDiffOn_holoMap hU (hf.2 p.1.1 c)).contDiffAt (hU.mem_nhds hmem)
  have hv : ψ p.crd = A.e c (f p.pt) := by simp only [hψ, Function.comp_apply, hinv]
  have hg : MContDiffAt ∞ (fun u => G ((A.e c).symm u)) (ψ p.crd) := hv ▸ (hG.2 c hc).self_of_nhds
  have hu : IsUnit (G ((A.e c).symm (ψ p.crd))).det := by rw [hv, (A.e c).left_inv hc]; exact hG.1
  have h1 := ((GlobalTheory.T.curvature_power_pullback_holomorphic n n' r (fun u => G ((A.e c).symm u)) ψ p.crd (hs.of_le (by norm_cast)) hg hu).2 j).2
  have hg' : MContDiffAt ∞ (fun x => G ((A.e c).symm (ψ x))) p.crd := fun a b =>
    (hg a b).comp p.crd (hs.restrict_scalars ℝ)
  have hTu : IsUnit (T (p.ch.symm p.crd)).det := by rw [hinv]; exact hT.1
  have hTd := hT.2 p.1.1 hp
  have ht : Tendsto p.ch.symm (𝓝 p.crd) (𝓝 p.pt) := by
    have := p.ch.continuousAt_symm (p.ch.map_source hp)
    rwa [ContinuousAt, p.ch.left_inv hp] at this
  have he : ∀ᶠ x in 𝓝 p.crd, G' (p.ch.symm x) =
      T (p.ch.symm x) * G ((A.e c).symm (ψ x)) * (T (p.ch.symm x))ᴴ := by
    filter_upwards [ht.eventually h, hU.mem_nhds hmem] with x hx hx'
    rw [hx]
    simp only [hψ, Function.comp_apply]
    rw [(A.e c).left_inv hx'.2]
  have h2 := (GlobalTheory.T.chernTransgression_forms_frame_invariant n' r _ _ (fun x => G' (p.ch.symm x)) (fun x => G' (p.ch.symm x)) (fun x => T (p.ch.symm x))
    (fun x => T (p.ch.symm x)) (fun x => T (p.ch.symm x)) p.crd hg' hu hg' hu hTd hTu hTd hTu hTd hTu
    (he.mono fun x hx => ⟨hx, hx⟩) j).2.1
  show pull _ (chernAt _ (A.e c (f p.pt)) j : Alt n) = (chernAt (fun v => G' (p.ch.symm v)) p.crd j : Alt n')
  rw [h2, h1, hv]

theorem pullback_chernF : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X Y : Var F) (ι : Type) [Finite ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X) (hf : f ≫ X.str = Y.str), Refines E E' φ f → ∀ H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ, IsMetricOn E ⊤ H → ∀ x : ι × ℕ, (atlas X σ).pullback (atlas Y σ) (ptMap σ f hf) (fld (atlas X σ) (chernF E H x)) = fld (atlas Y σ) (chernF E' (pullGram E H φ f hf) x) := by
  intro F _ σ X Y ι _ m E E' φ f hf hR H hH x
  funext p
  have hol := GlobalTheory.T.varietyComplexPointsMap_isHolomorphic F σ X Y f hf
  have hE := GlobalTheory.T.pulled_back_gram_matrices_independent_of_frame F σ X Y ι m E E' φ f hf hR H hH
  have hA := (E.nonempty (under (ptMap σ f hf p.pt))).choose_spec
  have hB := (E'.nonempty (under p.pt)).choose_spec
  have hP := hR.sub (under p.pt) _ hB _ (by
    have := hA
    exact (congrArg (fun w => (E.nonempty (under (ptMap σ f hf p.pt))).choose ∈ E.S w) (hE p.pt).1).mp this) x.1
  refine pull_chern_of_eventually (atlas X σ) (atlas Y σ) hol (gramAt E H x.1 (ptMap σ f hf p.pt))
    (gramAt E' (pullGram E H φ f hf) x.1 p.pt)
    (fun z => (((E'.nonempty (under p.pt)).choose *
      (Mat.map (E.nonempty (under (ptMap σ f hf p.pt))).choose φ)⁻¹) x.1).map (ratVal · z)) p _ _
    (GlobalTheory.T.flaggedBundleMetric_smoothUnit_etaleChart F σ X ι m 0 E H (isMetricFr_of_isMetricOn hH) _ _ hA x.1).1
    (GlobalTheory.T.isHolomorphicUnitMatrixAt_rational_matrix_values F σ Y _ _ p.pt (fun i j => mem_O_ratOf.1 (hP.1 i j)) hP.2.1 (mem_O_ratOf.1 hP.2.2.1)) ?_ x.2
  filter_upwards [(hol.1.tendsto p.pt).eventually (GlobalTheory.T.adaptedFrame_eventually_frame_near_complex_point F σ X ι m 0 E _ _ hA),
    GlobalTheory.T.adaptedFrame_eventually_frame_near_complex_point F σ Y ι m m E' _ _ hB] with z h1 h2
  exact (hE z).2 _ ((congrArg (fun w => (E.nonempty (under (ptMap σ f hf p.pt))).choose ∈ E.S w) (hE z).1).mp h1) _ h2 x.1

end GlobalTheory.ChernCalc
