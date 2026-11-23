import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.BsLApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullOfValuesSesq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffAtFlagCellGradedLinePotentialStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullGramFlagCellFrameStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagCellCoordinatesContDiffAtEtaleChartStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenFlagBundleCellAndCoordsRegularStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedFrameEventuallyFrameNearComplexPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramLowerTriangularFactorLowerTriangularConjStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramLowerTriangularFactorPosDefPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlaggedBundleMetricSmoothUnitEtaleChartStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFlaggedBundleMetricPullGramRefinementStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHolomorphicUnitMatrixAtRationalMatrixValuesStatement

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

namespace GlobalTheory.FlagCell2.GradedPull

theorem ratVal_zero' {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} (y : CxPts X.str σ) :
    ratVal (0 : X.Fn) y = 0 := by
  have e := ratVal_fnOf (y := y) mem_ptsIn_top trivial (0 : Γ(X.X, ⊤))
  rw [map_zero, ev_eq mem_ptsIn_top, map_zero] at e
  exact e

theorem ofValues_ddc_eq {n : ℕ} {p u : V n → ℝ} {Φ : V n → V n} {g : V n → ℂ} {z w : V n} (hw : Φ z = w)
    (hu : ContDiffAt ℝ 2 u w) (hΦ : ContDiffAt ℂ 2 Φ z) (hg : ∀ᶠ v in 𝓝 z, DifferentiableAt ℂ g v) (h0 : g z ≠ 0)
    (h : p =ᶠ[𝓝 z] fun v => u (Φ v) - Real.log (‖g v‖ ^ 2)) :
    (ofValues (ddc p z) : Alt n) = pull (fderiv ℂ Φ z) (ofValues (ddc u w) : Ev n) := by
  subst hw
  obtain ⟨U, hU, hUo, hz⟩ := eventually_nhds_iff.1 hg
  have hg2 : ContDiffAt ℂ 2 g z := ((ReciprocityTheory.L2DbarEstimates.contDiffOn_of_differentiableOn n g U hUo
    fun v hv => (hU v hv).differentiableWithinAt).contDiffAt (hUo.mem_nhds hz)).of_le (by norm_cast)
  have hs : IsSesq (ddc u (Φ z)) := by
    constructor <;> intros <;> simp [ddc] <;> ring
  rw [GlobalTheory.SecForm.pull_ofValues _ _ hs]
  congr 2
  funext ξ η
  have h1 : ContDiffAt ℝ 2 (fun v => u (Φ v)) z := hu.comp z (hΦ.restrict_scalars ℝ)
  have h2 : ContDiffAt ℝ 2 (fun v => Real.log (‖g v‖ ^ 2)) z :=
    ((hg2.restrict_scalars ℝ).norm_sq ℂ).log (by simpa using h0)
  rw [ddc, ddc, leviForm_congr h, leviForm_sub h1 h2, leviForm_log_normSq_eq_zero hg2 h0, sub_zero,
    leviForm_comp_holo hu hΦ]

theorem grF_eq_pull : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X Y : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X) (hf : f ≫ X.str = Y.str), Refines E E' φ f → ∀ (c : AlgChart X.str σ X.dim) (A : Mat m X.Fn) (u : Cell m → Y.Fn), ∀ H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ, IsMetricOn E ⊤ H → ∀ (ε : Fin Y.dim ≃ Fin X.dim ⊕ Cell m) (x : (atlas Y σ).Pt), x.pt ∈ cellSet E E' φ f hf c A u → ∀ r : Root m, (grF E' (pullGram E H φ f hf) r x : Alt Y.dim) = pull (fderiv ℂ (cellMap ε f hf c u ∘ x.ch.symm) x.crd) (ofValues (ddc (cellPot ε (fun v => H A (c.e.symm v)) r) (cellMap ε f hf c u x.pt)) : Ev Y.dim) := by
  intro F _ σ X Y ι _ m E E' φ f hf hR c A u H hH ε x hx r
  have hM := GlobalTheory.T.isFlaggedBundleMetric_pullGram_refinement F σ X Y ι m E E' φ f hf hR H hH
  set B₀ := (E'.nonempty (under x.pt)).choose with hB₀
  have hB₀m : B₀ ∈ E'.S (under x.pt) := (E'.nonempty (under x.pt)).choose_spec
  set B := upM u * A.map φ with hB
  have hT : ∀ w : CxPts Y.str σ, B ∈ E'.S (under w) → B₀ ∈ E'.S (under w) →
      HolUnitAt (atlas Y σ) (fun z => ((B₀ * B⁻¹) r.1).map (ratVal · z)) w ∧
      ∀ i j : Fin (m r.1), i < j → ((B₀ * B⁻¹) r.1).map (ratVal · w) i j = 0 := by
    intro w hAw hBw
    have hp := ((Fr.mem_iff hAw).1 hBw) r.1
    refine ⟨GlobalTheory.T.isHolomorphicUnitMatrixAt_rational_matrix_values F σ Y (m r.1) ((B₀ * B⁻¹) r.1) w (fun i j => mem_O_ratOf.1 (hp.1 i j)) hp.2.1
      (mem_O_ratOf.1 hp.2.2.1), fun i j hij => ?_⟩
    rw [Matrix.map_apply, hp.2.2.2 i j i.2 hij]
    exact ratVal_zero' w
  have hne : ∀ w : CxPts Y.str σ, B ∈ E'.S (under w) → B₀ ∈ E'.S (under w) →
      ((B₀ * B⁻¹) r.1).map (ratVal · w) r.2 r.2 ≠ 0 := fun w h1 h2 => by
    obtain ⟨hol, tri⟩ := hT w h1 h2
    have := hol.1.ne_zero
    rw [Matrix.det_of_lowerTriangular _ (fun i j hij => tri i j hij)] at this
    exact Finset.prod_ne_zero_iff.1 this r.2 (Finset.mem_univ _)
  have hπ : Continuous (ptMap σ f hf) := by
    unfold ptMap
    apply GlobalTheory.Points.PtsOver.continuous_map
  have hAπ : A ∈ E.S (under (ptMap σ f hf x.pt)) := hx.1.1
  have hsm := ((GlobalTheory.T.flaggedBundleMetric_smoothUnit_etaleChart F σ X ι m 0 E H (isMetricFr_of_isMetricOn hH) _ A hAπ r.1).2 c hx.2).self_of_nhds
  have hb : bsL ε (cellMap ε f hf c u x.pt) = c.e (ptMap σ f hf x.pt) := bsL_pt _ _ _
  have hu := (GlobalTheory.T.contDiffAt_flagCellGradedLinePotential ι m Y.dim X.dim ε (fun v => H A (c.e.symm v)) (cellMap ε f hf c u x.pt) r
    (by rw [hb]; exact hsm.2) (by rw [hb]; exact fun i j => (hsm.1 i j).of_le (by norm_cast))).1
  have hl : x.ch.symm x.crd = x.pt := x.ch.left_inv x.2
  have ht : Tendsto x.ch.symm (𝓝 x.crd) (𝓝 x.pt) := by
    have := x.ch.continuousAt_symm (x.ch.map_source x.2)
    rwa [ContinuousAt, x.ch.left_inv x.2] at this
  have e1 : ∀ᶠ z in 𝓝 x.pt, InCell E E' φ f A u (under z) :=
    (isOpen_ptsIn (p := Y.str) (σ := σ) ⟨_, (GlobalTheory.T.isOpen_flagBundleCell_and_coords_regular F X Y ι m E E' φ f hR A u).1⟩).mem_nhds (mem_ptsIn.2 hx.1)
      |> fun h => Filter.mem_of_superset h fun z hz => mem_ptsIn.1 hz
  have e2 := GlobalTheory.T.adaptedFrame_eventually_frame_near_complex_point F σ Y ι m m E' x.pt B₀ hB₀m
  have e3 : ∀ᶠ z in 𝓝 x.pt, ptMap σ f hf z ∈ c.e.source := hπ.continuousAt.eventually (c.e.open_source.mem_nhds hx.2)
  refine ofValues_ddc_eq (g := fun v => ((B₀ * B⁻¹) r.1).map (ratVal · (x.ch.symm v)) r.2 r.2)
    (congrArg (cellMap ε f hf c u) hl) hu (GlobalTheory.T.flagCellCoordinates_contDiffAt_etaleChart F σ X Y ι m E E' φ f hf hR c A u _ ε x hx)
    ((hT _ hx.1.2 hB₀m).1.2 x.1.1 x.2 r.2 r.2) (by rw [hl]; exact hne _ hx.1.2 hB₀m) ?_
  filter_upwards [ht.eventually e1, ht.eventually e2, ht.eventually e3] with v h1 h2 h3
  obtain ⟨hol, tri⟩ := hT _ h1.2 h2
  have hpd := hM.posDef _ B h1.2 r.1
  have e := hM.trans _ B h1.2 B₀ h2 r.1
  have e' := (GlobalTheory.T.gramLowerTriangularFactor_lowerTriangular_conj _ _ _ hpd tri hol.1).2 r.2
  have hpos := ((GlobalTheory.T.gramLowerTriangularFactor_posDef_properties _ _ hpd).2.1 r.2).1
  have eg := congrFun (GlobalTheory.T.pullGram_flagCell_frame F σ X Y ι m E E' φ f hf hR c A u H hH _ h1) r.1
  have ec : cellPot ε (fun v => H A (c.e.symm v)) r (cellMap ε f hf c u (x.ch.symm v)) =
      -Real.log (grD (pullGram E H φ f hf B (x.ch.symm v) r.1) r.2) := by
    rw [hB, eg, cellPot, cellMap, bsL_pt, fb_pt, c.e.left_inv h3]
  show -Real.log (grD (pullGram E H φ f hf B₀ (x.ch.symm v) r.1) r.2) =
    cellPot ε (fun v => H A (c.e.symm v)) r (cellMap ε f hf c u (x.ch.symm v)) - _
  rw [ec, e]
  erw [e']
  rw [Real.log_mul (pow_ne_zero _ (norm_ne_zero_iff.2 (hne _ h1.2 h2))) hpos.ne']
  ring

end GlobalTheory.FlagCell2.GradedPull
