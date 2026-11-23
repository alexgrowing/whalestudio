import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PointPoly
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FirstIndexEqOfUnfolded
import Formalism.DegreeFormula.Statement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MeasurePreservingCompEquiv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopChernDensityInvariantHolomorphicFrameChange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniformisationComponentEqOfSameModulusPoint
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHolomorphicInvertibleFrameCoordinates
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrameCoordinatesEqRationalMatrixValuesChartStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GramSmoothOfHolomorphicFrames
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHolomorphicChartOfExpChartGenericFibre
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsConjFsBasisOfUnitary
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open MeasureTheory Formalism.DegreeFormula GlobalTheory.TrueCx
open scoped Matrix
open Filter Topology
open GlobalTheory.PointChern

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.UnifFrameChange

theorem isHolTo_cxPt_V {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} (Z : Model Xo c β) {σ : c.F →+* ℂ}
    {r : ℕ} {U : Formalism.L2.PjFree.Unf Xo c σ r} (hU : Formalism.L2.PjFree.IsUnf U) (k : U.Comp) {n : ℕ}
    {B : Set (ReciprocityTheory.L2DbarEstimates.V n)} (hB : IsOpen B) (x : ReciprocityTheory.L2DbarEstimates.V n → (U.X k).dom)
    (hd : ∀ τ a a', DifferentiableOn ℂ (fun b => ReciprocityTheory.ChartRestriction.G.FD.mat (x b).1 τ a a') B) :
    IsHolTo B fun b => (cxPt Z (U.un k (x b))).1 := by
  let L := EuclideanSpace.equiv (Fin n) ℂ
  have hB₁ : IsOpen (L.symm ⁻¹' B) := hB.preimage L.symm.continuous
  have h1 := GlobalTheory.GramFamily.isHolTo_cxPt Z hU k hB₁ (fun u => x (L.symm u)) fun τ a a' =>
    (hd τ a a').comp L.symm.differentiableOn fun u hu => hu
  intro W f
  obtain ⟨ho, hdf⟩ := h1 W f
  have hset : {b ∈ B | ⊤ ≤ (cxPt Z (U.un k (x b))).1 ⁻¹ᵁ W} =
      L ⁻¹' {u ∈ L.symm ⁻¹' B | ⊤ ≤ (cxPt Z (U.un k (x (L.symm u)))).1 ⁻¹ᵁ W} := by
    ext b
    simp only [Set.mem_setOf_eq, Set.mem_preimage, ContinuousLinearEquiv.symm_apply_apply]
  rw [hset]
  refine ⟨ho.preimage L.continuous, ?_⟩
  have := hdf.comp L.differentiableOn (Set.mapsTo_preimage _ _)
  refine this.congr fun b _ => ?_
  simp only [Function.comp_apply, ContinuousLinearEquiv.symm_apply_apply]

end GlobalTheory.UnifFrameChange

open GlobalTheory.UnifFrameChange in

theorem GlobalTheory.UnifFrameChange.exists_holomorphic_frame_change : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (k : U.Comp) (X : Var F) (j : X.X ⟶ gen T.Z) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsOpenImmersion j → Tied e X j f₀ Eb A₀ → ∀ ψ : ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p) → ℂ) → CxPts X.str (σ.comp e.toRingHom), (∀ x : (U.X k).dom, cxOf e σ hj (ψ (flat (domPt (U.X k) (Nat.le_add_right Dw.p Dw.q) (Equiv.refl (U.X k).Ψ) x.1))) = cxPt T.Z (U.un k x)) → ∀ (h : Fintype.card ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p)) = X.dim) (v : ReciprocityTheory.L2DbarEstimates.V X.dim), GlobalTheory.UnifDens.flatL h v ∈ DomFlat (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p) → ∀ A ∈ Eb.S (under (ψ (GlobalTheory.UnifDens.flatL h v))), ∀ s : ReciprocityTheory.L2DbarEstimates.V X.dim → ReciprocityTheory.ChartRestriction.G.FD.Frame (U.X k).Ψ (Dw.p + Dw.q), AnalyticAt ℂ s v → (∀ᶠ w in nhds v, ∃ hs : s w ∈ (U.X k).dom, flat (domPt (U.X k) (Nat.le_add_right Dw.p Dw.q) (Equiv.refl (U.X k).Ψ) (s w)) = GlobalTheory.UnifDens.flatL h w) → ∃ K : ReciprocityTheory.L2DbarEstimates.V X.dim → Mat Dw.mult ℂ, (∀ τ a b, AnalyticAt ℂ (fun w => K w τ a b) v) ∧ (∀ τ, IsUnit (K v τ).det) ∧ ∀ᶠ w in nhds v, ∀ (hs : s w ∈ (U.X k).dom) (g : EigFrame T.Z σ ((cxOf e σ hj (ψ (GlobalTheory.UnifDens.flatL h w))).1 ≫ genι T.Z)), FrameAt e f₀ A₀ A (ψ (GlobalTheory.UnifDens.flatL h w)) g → ∀ (M : EigMet T.Z σ) (τ : E →+* ℂ), M.gram (cxOf e σ hj (ψ (GlobalTheory.UnifDens.flatL h w))) g τ = (K w τ)ᴴ * M.gram (cxPt T.Z (U.un k ⟨s w, hs⟩)) (cxFrame T.Z (U.un k ⟨s w, hs⟩)) τ * K w τ := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ U _ hU k X j f₀ Eb A₀ hj hoi hT ψ hψ h v _ A hA s han hlift
  classical

  set pt : ReciprocityTheory.L2DbarEstimates.V X.dim → CxPts X.str (σ.comp e.toRingHom) := fun w => ψ (GlobalTheory.UnifDens.flatL h w) with hptdef

  obtain ⟨B₀, hB₀all, hB₀, hv₀⟩ := eventually_nhds_iff.1 (hlift.and han.eventually_analyticAt)
  choose hsB₀ hflB₀ using fun b (hb : b ∈ B₀) => (hB₀all b hb).1
  have hpt₀ : ∀ b (hb : b ∈ B₀), cxPt T.Z (U.un k ⟨s b, hsB₀ b hb⟩) = cxOf e σ hj (pt b) := by
    intro b hb
    have := hψ ⟨s b, hsB₀ b hb⟩
    rw [hflB₀ b hb] at this
    exact this.symm
  let x : ReciprocityTheory.L2DbarEstimates.V X.dim → (U.X k).dom := fun b =>
    if hb : b ∈ B₀ then ⟨s b, hsB₀ b hb⟩ else ⟨s v, hsB₀ v hv₀⟩
  have hxB : ∀ b (hb : b ∈ B₀), x b = ⟨s b, hsB₀ b hb⟩ := fun b hb => by simp only [x, dif_pos hb]
  have hsd : DifferentiableOn ℂ s B₀ := fun b hb => (hB₀all b hb).2.differentiableAt.differentiableWithinAt
  have hd : ∀ τ a a', DifferentiableOn ℂ (fun b => ReciprocityTheory.ChartRestriction.G.FD.mat (x b).1 τ a a') B₀ := by
    intro τ a a'
    refine (differentiableOn_pi.1 (differentiableOn_pi.1 (differentiableOn_pi.1 hsd τ) a) a').congr fun b hb => ?_
    rw [hxB b hb]
    rfl
  have hY := isHolTo_cxPt_V T.Z hU k hB₀ x hd
  have hxpt : ∀ b (hb : b ∈ B₀), (cxPt T.Z (U.un k (x b))) = cxOf e σ hj (pt b) := fun b hb => by
    rw [hxB b hb]; exact hpt₀ b hb

  have hgenev : ∀ W' : (gen T.Z).Opens, cxOf e σ hj (pt v) ∈ ptsIn (genStr T.Z) σ W' →
      ∀ᶠ w in 𝓝 v, w ∈ B₀ ∧ ⊤ ≤ (cxPt T.Z (U.un k (x w))).1 ⁻¹ᵁ W' := by
    intro W' hW'
    refine ((hY W' 0).1).mem_nhds ⟨hv₀, ?_⟩
    show ⊤ ≤ (cxPt T.Z (U.un k (x v))).1 ⁻¹ᵁ W'
    rw [hxpt v hv₀]
    exact hW'
  have hpre : ∀ (W : X.X.Opens) (z : CxPts X.str (σ.comp e.toRingHom)),
      z ∈ ptsIn X.str (σ.comp e.toRingHom) W ↔ cxOf e σ hj z ∈ ptsIn (genStr T.Z) σ (j ''ᵁ W) := by
    intro W z
    have := mem_ptsIn_preimage (m := cxOf e σ hj) (f := j) (fun _ => rfl) (U := j ''ᵁ W) (z := z)
    rwa [j.preimage_image_eq W] at this
  have hXev : ∀ W : X.X.Opens, pt v ∈ ptsIn X.str (σ.comp e.toRingHom) W →
      ∀ᶠ w in 𝓝 v, pt w ∈ ptsIn X.str (σ.comp e.toRingHom) W := by
    intro W hW
    filter_upwards [hgenev _ ((hpre W _).1 hW)] with w hw
    refine (hpre W _).2 ?_
    rw [← hxpt w hw.1]
    exact hw.2
  have hregev : ∀ {g : X.Fn}, RegAt (under (pt v)) g → ∀ᶠ w in 𝓝 v, RegAt (under (pt w)) g := by
    intro g hg
    obtain ⟨W, hW, a, rfl⟩ := hg.exists_fnOf
    filter_upwards [hXev W (mem_ptsIn.2 hW)] with w hw
    exact regAt_fnOf (mem_ptsIn.1 hw) _ a
  have hmemev : ∀ᶠ w in 𝓝 v, A ∈ Eb.S (under (pt w)) := by
    obtain ⟨U', B', hU', hB', hS⟩ := Eb.loc (under (pt v))
    have hP := (hS _ hU' A).1 hA
    have hU'' : ∀ᶠ w in 𝓝 v, under (pt w) ∈ U' := by
      filter_upwards [hXev U' (mem_ptsIn.2 hU')] with w hw
      exact mem_ptsIn.1 hw
    have h1 : ∀ᶠ w in 𝓝 v, ∀ τ, (∀ i j, RegAt (under (pt w)) ((A * B'⁻¹) τ i j)) ∧
        RegAt (under (pt w)) ((A * B'⁻¹) τ).det⁻¹ :=
      Filter.eventually_all.2 fun τ => (Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j =>
        hregev (mem_O_ratOf.1 ((hP τ).1 i j))).and (hregev (mem_O_ratOf.1 (hP τ).2.2.1))
    filter_upwards [hU'', h1] with w hw hw1
    exact (hS _ hw A).2 fun τ => ⟨fun i j => mem_O_ratOf.2 ((hw1 τ).1 i j), (hP τ).2.1, mem_O_ratOf.2 (hw1 τ).2,
      fun i j hi => absurd hi (by simp)⟩
  have hratan : ∀ {g : X.Fn}, RegAt (under (pt v)) g → AnalyticAt ℂ (fun w => ratVal g (pt w)) v := by
    intro g hg
    haveI : IsOpenImmersion j := hoi
    obtain ⟨W, hW, a, rfl⟩ := hg.exists_fnOf
    set g' := (j.appIso W).inv.hom a
    have hvS : v ∈ {b ∈ B₀ | ⊤ ≤ (cxPt T.Z (U.un k (x b))).1 ⁻¹ᵁ (j ''ᵁ W)} := by
      refine ⟨hv₀, ?_⟩
      rw [hxpt v hv₀]
      exact GlobalTheory.LieBase.le_preimage_cxOf e σ hj W (mem_ptsIn.2 hW)
    have han' := GlobalTheory.SCV.analyticAt_of_differentiableOn ((hY (j ''ᵁ W) g').2) (((hY (j ''ᵁ W) g').1).mem_nhds hvS)
    refine han'.congr ?_
    filter_upwards [hXev W (mem_ptsIn.2 hW), hB₀.mem_nhds hv₀] with w hw hwB
    show valAt' _ _ _ = ratVal _ (pt w)
    rw [ratVal_fnOf hw, GlobalTheory.LieBase.ev_eq_valAt'_cxOf e σ hj W a hw, hxpt w hwB]

  obtain ⟨V₀, hV₀, φ, Φ, hzV, hφ, -⟩ := EigSpread.exists_stable_eigFrame E H Dw l Xo c O β T.Z
    ((cxOf e σ hj (pt v)).1 (IsLocalRing.closedPoint ℂ))
  let V : (gen T.Z).affineOpens := ⟨V₀, hV₀⟩
  have hφ' : LogKS.chart V ≫ genStr T.Z = spMap φ := hφ
  have hyV : cxOf e σ hj (pt v) ∈ ptsIn (genStr T.Z) σ V.1 := mem_ptsIn.2 hzV
  obtain ⟨M, hM⟩ := GlobalTheory.T.frame_coordinates_eq_rational_matrix_values_chart E H Dw l Xo c O β T.Z σ F e X j f₀ Eb A₀ hj hoi hT V φ Φ hφ' A
  have hVn : ∀ᶠ w in 𝓝 v, cxOf e σ hj (pt w) ∈ ptsIn (genStr T.Z) σ V.1 := by
    filter_upwards [hgenev _ hyV] with w hw
    rw [← hxpt w hw.1]
    exact hw.2
  obtain ⟨B, hBall, hB, hb₀⟩ := eventually_nhds_iff.1
    ((show ∀ᶠ w in 𝓝 v, w ∈ B₀ from hB₀.mem_nhds hv₀).and (hVn.and hmemev))
  have hsB : ∀ b ∈ B, s b ∈ (U.X k).dom := fun b hb => hsB₀ b (hBall b hb).1
  have hpt : ∀ b (hb : b ∈ B), cxPt T.Z (U.un k ⟨s b, hsB b hb⟩) = cxOf e σ hj (pt b) :=
    fun b hb => hpt₀ b (hBall b hb).1
  obtain ⟨N, hN, hNco⟩ := GlobalTheory.FrameLift.exists_coords (Z := T.Z) hU k hB hb₀ hsB
    (hsd.mono fun b hb => (hBall b hb).1) V Φ (fun b hb => by rw [hpt b hb]; exact (hBall b hb).2.1)
  have key : ∀ b (hb : b ∈ B) (G g : EigFrame T.Z σ ((cxOf e σ hj (pt b)).1 ≫ genι T.Z)),
      (∀ τ i, G.v τ i = (cxFrame T.Z (U.un k ⟨s b, hsB b hb⟩)).v τ i) → FrameAt e f₀ A₀ A (pt b) g →
        ∀ τ, G.co g τ = N b τ * (M τ).map fun r => ratVal r (pt b) := by
    intro b hb G g hG hg τ
    obtain ⟨-, hzV, hzS⟩ := hBall b hb
    have hov : σ = (evHom hzV).comp φ := by
      generalize cxOf e σ hj (pt b) = z at hzV
      exact GlobalTheory.ShFam.EigLoc.spMap_inj (z.2.symm.trans (by
        rw [← ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp_spMap, ← hφ', ← Category.assoc, GlobalTheory.LieMet.spMap_evHom hzV]))
    have hx : (cxOf e σ hj (pt b)).1 ≫ genι T.Z = spMap (evHom hzV) ≫ LogKS.chart V ≫ genι T.Z := by
      rw [← Category.assoc, GlobalTheory.LieMet.spMap_evHom hzV]
    obtain ⟨f, hf⟩ := Φ.exists_isMap (evHom hzV) hov hx
    rw [← hNco b hb _ (hpt b hb) hzV G f hG hf τ, ← (hM _ hzS hzV).2.2 g hg f hf τ, EigFrame.co_mul]
  have hex : ∀ b ∈ B, ∃ g : EigFrame T.Z σ ((cxOf e σ hj (pt b)).1 ≫ genι T.Z),
      FrameAt e f₀ A₀ A (pt b) g := fun b hb => (hM _ (hBall b hb).2.2 (hBall b hb).2.1).2.1
  refine ⟨fun b τ => N b τ * (M τ).map fun r => ratVal r (pt b), fun τ a a' => ?_, fun τ => ?_, ?_⟩
  · simp only [Matrix.mul_apply, Matrix.map_apply]
    exact Finset.analyticAt_fun_sum _ fun i _ =>
      (GlobalTheory.SCV.analyticAt_of_differentiableOn (hN τ a i) (hB.mem_nhds hb₀)).mul
        (hratan ((hM (pt v) hA hyV).1 τ i a'))
  · obtain ⟨g, hg⟩ := hex _ hb₀
    obtain ⟨G, hG, -⟩ := GlobalTheory.FrameLift.exists_transport (hpt _ hb₀) (cxFrame T.Z _)
    show IsUnit (N v τ * (M τ).map fun r => ratVal r (pt v)).det
    rw [← key _ hb₀ G g hG hg τ]
    exact G.isUnit_det_co g τ
  · filter_upwards [hB.mem_nhds hb₀] with b hb
    intro hsb g hg Me τ
    obtain ⟨G, hG, hGm⟩ := GlobalTheory.FrameLift.exists_transport (hpt b hb) (cxFrame T.Z _)
    rw [← key b hb G g hG hg τ, ← hGm Me τ]
    exact Me.change _ G g τ

end
