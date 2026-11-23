import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MultOfNotMem
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HodgeMetricUniformisationSmoothOnInterior
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsHolToOfOpenImmersion
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExpCoordinatesTangentFieldHolomorphicPeriodMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrameCoordinatesEqRationalMatrixValuesChartStatement
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn

set_option autoImplicit false

noncomputable section

section SlopeTestRemainingChoices

open AlgebraicGeometry CategoryTheory Limits NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.ShFam
open GlobalTheory.ArcQ GlobalTheory.FlagBundle Filter Topology

namespace GlobalTheory.FrameLift

open GlobalTheory.ShFam.Hor.LogCh

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β} {σ : c.F →+* ℂ} {r : ℕ}

theorem nonempty_unfWit {U : Formalism.L2.PjFree.Unf Xo c σ r} (hU : Formalism.L2.PjFree.IsUnf U) : Nonempty (UnfWit U) := by
  obtain ⟨-, -, -, -, -, g, e, F, ik, φ, hiso, hP⟩ := hU
  choose Pm h1 h2 h3 h4 h5 using hP
  exact ⟨⟨g, e, F, ik, φ, hiso, Pm, h1, h2, fun k x => ⟨h3 k x, h4 k x⟩, h5⟩⟩

theorem exists_transport {p q : CxPts (genStr Z) σ} (h : p = q) (G : EigFrame Z σ (p.1 ≫ genι Z)) :
    ∃ G' : EigFrame Z σ (q.1 ≫ genι Z), (∀ τ i, G'.v τ i = G.v τ i) ∧
      ∀ (M : EigMet Z σ) τ, M.gram q G' τ = M.gram p G τ := by
  subst h
  exact ⟨G, fun _ _ => rfl, fun _ _ => rfl⟩

theorem exists_coords {U : Formalism.L2.PjFree.Unf Xo c σ r} (hU : Formalism.L2.PjFree.IsUnf U) (k : U.Comp) {n : ℕ}
    {B : Set (ReciprocityTheory.L2DbarEstimates.V n)} (hB : IsOpen B) {b₀ : ReciprocityTheory.L2DbarEstimates.V n} (hb₀ : b₀ ∈ B)
    {s : ReciprocityTheory.L2DbarEstimates.V n → ReciprocityTheory.ChartRestriction.G.FD.Frame (U.X k).Ψ r} (hs : ∀ b ∈ B, s b ∈ (U.X k).dom)
    (hd : DifferentiableOn ℂ s B) (V : (gen Z).affineOpens) {φ : c.F →+* Γ(gen Z, V.1)}
    (Φ : EigFrame Z φ (LogKS.chart V ≫ genι Z))
    (hV : ∀ b (hb : b ∈ B), cxPt Z (U.un k ⟨s b, hs b hb⟩) ∈ ptsIn (genStr Z) σ V.1) :
    ∃ N : ReciprocityTheory.L2DbarEstimates.V n → Mat Dw.mult ℂ, (∀ τ a a', DifferentiableOn ℂ (fun b => N b τ a a') B) ∧
      ∀ b (hb : b ∈ B) (y : CxPts (genStr Z) σ), cxPt Z (U.un k ⟨s b, hs b hb⟩) = y →
        ∀ (hy : y ∈ ptsIn (genStr Z) σ V.1) (G f : EigFrame Z σ (y.1 ≫ genι Z)),
          (∀ τ i, G.v τ i = (cxFrame Z (U.un k ⟨s b, hs b hb⟩)).v τ i) → Φ.IsMap (evHom hy) f →
            ∀ τ, G.co f τ = N b τ := by
  classical
  obtain ⟨W⟩ := nonempty_unfWit hU
  let L := EuclideanSpace.equiv (Fin n) ℂ
  set B₁ : Set (Fin n → ℂ) := L.symm ⁻¹' B with hB₁
  have hB₁o : IsOpen B₁ := hB.preimage L.symm.continuous
  let x : (Fin n → ℂ) → (U.X k).dom := fun v =>
    if h : L.symm v ∈ B then ⟨s (L.symm v), hs _ h⟩ else ⟨s b₀, hs _ hb₀⟩
  have hx : ∀ v ∈ B₁, (x v).1 = s (L.symm v) := fun v hv => by
    simp only [x, dif_pos (show L.symm v ∈ B from hv)]
  have hxL : ∀ b (hb : b ∈ B), x (L b) = ⟨s b, hs b hb⟩ := fun b hb =>
    Subtype.ext ((hx _ (by simpa [hB₁] using hb)).trans (by rw [ContinuousLinearEquiv.symm_apply_apply]))
  have hsd : DifferentiableOn ℂ (fun v => s (L.symm v)) B₁ := hd.comp L.symm.differentiableOn fun v hv => hv
  have hPd : ∀ a, DifferentiableOn ℂ (fun v => W.Pm k (x v) a) B₁ := fun a => differentiableOn_pi.2 fun j =>
    (GlobalTheory.TrueCx.TorHolo.differentiableOn_perFr (U.X k) (x := fun v => s (L.symm v)) (fun v hv => hs _ hv)
      (fun τ a a' => differentiableOn_pi.1 (differentiableOn_pi.1 (differentiableOn_pi.1 hsd τ) a) a') _ _ _).congr
      fun v hv => by rw [W.Pm_eq, hx v hv]
  let p : (Fin n → ℂ) → (Sp ℂ ⟶ Xo.XF c) := fun v => GlobalTheory.AllWt.ptF (S := CAt σ) (U.un k (x v))
  have hu : ∀ v, W.F.u (W.ik k) (W.Pm k (x v)) =
      p v ≫ pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) :=
    fun v => (W.lie k (x v)).1.symm.trans (ptF_fst (U.un k (x v))).symm
  have hp : ∀ v, p v ≫ pullback.snd _ _ = spMap σ := fun v => ptF_snd (U.un k (x v))
  choose Y hY hYd using fun (a : Σ τ : E →+* ℂ, Fin (Dw.mult τ)) =>
    GlobalTheory.ModelExpCoord.coord_holomorphic _ _ _ _ _ _ _ _ Z σ W.g _ W.F (W.ik k) n B₁ (fun v => W.Pm k (x v)) p hu V
      (Φ.v a.1 a.2) hB₁o (fun v => W.period k (x v)) hPd hp (Φ.tan a.1 a.2)
  refine ⟨fun b τ => of fun a a' => Y ⟨τ, a'⟩ (L b) (W.e.symm ⟨τ, a⟩), fun τ a a' => ?_, fun b hb y hq hy G f hG hf τ => ?_⟩
  · refine differentiableOn_pi.1 ((hY ⟨τ, a'⟩).comp L.differentiableOn fun b hb => ⟨by simpa [hB₁] using hb, ?_⟩) _
    show ⊤ ≤ (cxPt Z (U.un k (x (L b)))).1 ⁻¹ᵁ V.1
    rw [hxL b hb]
    exact hV b hb
  · ext a a'
    obtain ⟨w, hwt, hwm, hwc⟩ := GlobalTheory.HodgeSmooth.exists_lift_comb _ hq G f hG τ a'
    have h1 := hYd ⟨τ, a'⟩ (L b) (by simpa [hB₁] using hb) y hy (by
      show _ = (cxPt Z (U.un k (x (L b)))).1
      rw [hxL b hb, hq])
    have hfv : spMap (dualMap (evHom hy)) ≫ Φ.v τ a' = w ≫ Z.m.φ := by rw [hwm, hf τ a']
    rw [hfv] at h1
    have hbase : w ≫ Z.oF.t.G.hom = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ p (L b) := by
      show _ = _ ≫ GlobalTheory.AllWt.ptF (S := CAt σ) (U.un k (x (L b)))
      rw [hxL b hb]
      exact hwt.1
    have h2 := isDerivAt0_ex_of_push Z W.F (p (L b)) (W.ik k) (W.Pm k (x (L b))) (W.period k _) (hu _) hbase h1
    rw [hxL b hb] at h2
    have per := W.period k ⟨s b, hs b hb⟩
    obtain ⟨hPx, hv⟩ := W.lie k ⟨s b, hs b hb⟩
    have h3 := (DerLin.isCombAt_iff_isDerivAt0 E H Dw l Xo _ _ _ W.F _ _ per _ ((U.un k ⟨s b, hs b hb⟩).u τ) _ (hv τ) _
      _).1 (hPx ▸ hwc)
    have tn := isDerivAt0_ex_isTanAt E H Dw l Xo _ _ _ W.F _ _ per
    have h4 := congrFun ((tn.2.2 _ (tn.1 _ _ h2)).unique h2 h3) (W.e.symm ⟨τ, a⟩)
    have hi : ∀ j j' : Fin (Dw.mult τ), W.e.symm ⟨τ, j⟩ = W.e.symm ⟨τ, j'⟩ ↔ j = j' := fun j j' => by simp
    refine Eq.trans ?_ h4.symm
    simp [Finset.sum_apply, Pi.single_apply, hi]

variable {F : Type} [Field F] {X : Var F} {σ' : F →+* ℂ}

theorem eventually_regAt {y : CxPts X.str σ'} {g : X.Fn} (hg : RegAt (under y) g) : ∀ᶠ z in 𝓝 y, RegAt (under z) g := by
  obtain ⟨W, hW, a, rfl⟩ := hg.exists_fnOf
  filter_upwards [(isOpen_ptsIn W).mem_nhds (mem_ptsIn.2 hW)] with z hz
  exact regAt_fnOf (mem_ptsIn.1 hz) _ a

theorem eventually_mem {ι : Type} [Finite ι] {m : ι → ℕ} {S : Fr (ratOf X) m 0} {y : CxPts X.str σ'} {A : Mat m X.Fn}
    (hA : A ∈ S.S (under y)) : ∀ᶠ z in 𝓝 y, A ∈ S.S (under z) := by
  obtain ⟨U, B, hU, hB, hS⟩ := S.loc (under y)
  have hP := (hS _ hU A).1 hA
  have hU' : ∀ᶠ z in 𝓝 y, under z ∈ U := by
    filter_upwards [(isOpen_ptsIn U).mem_nhds (mem_ptsIn.2 hU)] with z hz
    exact mem_ptsIn.1 hz
  have h1 : ∀ᶠ z in 𝓝 y, ∀ τ, (∀ i j, RegAt (under z) ((A * B⁻¹) τ i j)) ∧ RegAt (under z) ((A * B⁻¹) τ).det⁻¹ :=
    Filter.eventually_all.2 fun τ => (Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j =>
      eventually_regAt (mem_O_ratOf.1 ((hP τ).1 i j))).and (eventually_regAt (mem_O_ratOf.1 (hP τ).2.2.1))
  filter_upwards [hU', h1] with z hz hz1
  exact (hS _ hz A).2 fun τ => ⟨fun i j => mem_O_ratOf.2 ((hz1 τ).1 i j), (hP τ).2.1, mem_O_ratOf.2 (hz1 τ).2,
    fun i j hi => absurd hi (by simp)⟩

theorem analyticAt_ratVal {d : ℕ} (ch : AlgChart X.str σ' d) {y : CxPts X.str σ'} (hy : y ∈ ch.e.source) {g : X.Fn}
    (hg : RegAt (under y) g) : AnalyticAt ℂ (fun w => ratVal g (ch.e.symm w)) (ch.e y) := by
  obtain ⟨W, hW, a, rfl⟩ := hg.exists_fnOf
  refine GlobalTheory.SCV.analyticAt_of_differentiableOn ((ch.holo W a).congr fun w hw => ratVal_fnOf hw.2 _ a)
    ((GlobalTheory.ChartGlue.isOpen_over ch.e (isOpen_ptsIn W)).mem_nhds ⟨ch.e.map_source hy, ?_⟩)
  show ch.e.symm (ch.e y) ∈ ptsIn X.str σ' W
  rw [ch.e.left_inv hy]
  exact mem_ptsIn.2 hW

end GlobalTheory.FrameLift

end SlopeTestRemainingChoices

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open GlobalTheory.PointChern Filter Topology
open scoped Matrix

theorem GlobalTheory.FrameLift.exists_holomorphic_frame_coords : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsOpenImmersion j → Tied e X j f₀ Eb A₀ → ∀ y ∈ ptsIn X.str (σ.comp e.toRingHom) (openPart j), ∀ c' : AlgChart X.str (σ.comp e.toRingHom) X.dim, y ∈ c'.e.source → ∀ A ∈ Eb.S (under y), ∀ (k' : U.Comp) (s : ReciprocityTheory.L2DbarEstimates.V X.dim → ReciprocityTheory.ChartRestriction.G.FD.Frame (U.X k').Ψ (Dw.p + Dw.q)), AnalyticAt ℂ s (c'.e y) → (∀ᶠ w in 𝓝 (c'.e y), ∃ hs : s w ∈ (U.X k').dom, cxPt T.Z (U.un k' ⟨s w, hs⟩) = cxOf e σ hj (c'.e.symm w)) → ∃ K : ReciprocityTheory.L2DbarEstimates.V X.dim → Mat Dw.mult ℂ, (∀ τ a b, AnalyticAt ℂ (fun w => K w τ a b) (c'.e y)) ∧ (∀ τ, IsUnit (K (c'.e y) τ).det) ∧ ∀ᶠ w in 𝓝 (c'.e y), (∃ g : EigFrame T.Z σ ((cxOf e σ hj (c'.e.symm w)).1 ≫ genι T.Z), FrameAt e f₀ A₀ A (c'.e.symm w) g) ∧ ∀ (hs : s w ∈ (U.X k').dom) (g : EigFrame T.Z σ ((cxOf e σ hj (c'.e.symm w)).1 ≫ genι T.Z)), FrameAt e f₀ A₀ A (c'.e.symm w) g → ∀ (M : EigMet T.Z σ) (τ : E →+* ℂ), M.gram (cxOf e σ hj (c'.e.symm w)) g τ = (K w τ)ᴴ * M.gram (cxPt T.Z (U.un k' ⟨s w, hs⟩)) (cxFrame T.Z (U.un k' ⟨s w, hs⟩)) τ * K w τ := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ U _ hU X j f₀ Eb A₀ hj hoi hT y _ c' hyc A hA k' s hs hlift
  obtain ⟨V₀, hV₀, φ, Φ, hzV, hφ, -⟩ := EigSpread.exists_stable_eigFrame E H Dw l Xo c O β T.Z
    ((cxOf e σ hj y).1 (IsLocalRing.closedPoint ℂ))
  let V : (gen T.Z).affineOpens := ⟨V₀, hV₀⟩
  have hφ' : LogKS.chart V ≫ genStr T.Z = spMap φ := hφ
  have hyV : cxOf e σ hj y ∈ ptsIn (genStr T.Z) σ V.1 := mem_ptsIn.2 hzV
  obtain ⟨M, hM⟩ := GlobalTheory.T.frame_coordinates_eq_rational_matrix_values_chart E H Dw l Xo c O β T.Z σ F e X j f₀ Eb A₀ hj hoi hT V φ Φ hφ' A
  have hpre : ∀ z : GlobalTheory.CxPts X.str (σ.comp e.toRingHom),
      z ∈ ptsIn X.str (σ.comp e.toRingHom) (j ⁻¹ᵁ V.1) ↔ cxOf e σ hj z ∈ ptsIn (genStr T.Z) σ V.1 :=
    fun z => mem_ptsIn_preimage (m := cxOf e σ hj) (f := j) (fun _ => rfl)
  have hVn : ∀ᶠ z in 𝓝 y, cxOf e σ hj z ∈ ptsIn (genStr T.Z) σ V.1 := by
    filter_upwards [(isOpen_ptsIn _).mem_nhds ((hpre y).2 hyV)] with z hz
    exact (hpre z).1 hz
  have htend : Tendsto c'.e.symm (𝓝 (c'.e y)) (𝓝 y) := c'.e.tendsto_symm hyc
  obtain ⟨B, hBall, hB, hb₀⟩ := eventually_nhds_iff.1 ((hlift.and hs.eventually_analyticAt).and
    (htend.eventually (hVn.and (GlobalTheory.FrameLift.eventually_mem hA))))
  choose hsB hpt using fun b hb => (hBall b hb).1.1
  obtain ⟨N, hN, hNco⟩ := GlobalTheory.FrameLift.exists_coords (Z := T.Z) hU k' hB hb₀ hsB
    (fun b hb => (hBall b hb).1.2.differentiableAt.differentiableWithinAt) V Φ
    (fun b hb => by rw [hpt b hb]; exact (hBall b hb).2.1)
  have key : ∀ b (hb : b ∈ B) (G g : EigFrame T.Z σ ((cxOf e σ hj (c'.e.symm b)).1 ≫ genι T.Z)),
      (∀ τ i, G.v τ i = (cxFrame T.Z (U.un k' ⟨s b, hsB b hb⟩)).v τ i) → FrameAt e f₀ A₀ A (c'.e.symm b) g →
        ∀ τ, G.co g τ = N b τ * (M τ).map fun r => ratVal r (c'.e.symm b) := by
    intro b hb G g hG hg τ
    obtain ⟨-, hzV, hzS⟩ := hBall b hb
    have hov : σ = (evHom hzV).comp φ := by
      generalize cxOf e σ hj (c'.e.symm b) = z at hzV
      exact GlobalTheory.ShFam.EigLoc.spMap_inj (z.2.symm.trans (by
        rw [← ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp_spMap, ← hφ', ← Category.assoc, GlobalTheory.LieMet.spMap_evHom hzV]))
    have hx : (cxOf e σ hj (c'.e.symm b)).1 ≫ genι T.Z = spMap (evHom hzV) ≫ LogKS.chart V ≫ genι T.Z := by
      rw [← Category.assoc, GlobalTheory.LieMet.spMap_evHom hzV]
    obtain ⟨f, hf⟩ := Φ.exists_isMap (evHom hzV) hov hx
    rw [← hNco b hb _ (hpt b hb) hzV G f hG hf τ, ← (hM _ hzS hzV).2.2 g hg f hf τ, EigFrame.co_mul]
  have hex : ∀ b ∈ B, ∃ g : EigFrame T.Z σ ((cxOf e σ hj (c'.e.symm b)).1 ≫ genι T.Z),
      FrameAt e f₀ A₀ A (c'.e.symm b) g := fun b hb => (hM _ (hBall b hb).2.2 (hBall b hb).2.1).2.1
  refine ⟨fun b τ => N b τ * (M τ).map fun r => ratVal r (c'.e.symm b), fun τ a a' => ?_, fun τ => ?_, ?_⟩
  · simp only [Matrix.mul_apply, Matrix.map_apply]
    exact Finset.analyticAt_fun_sum _ fun i _ =>
      (GlobalTheory.SCV.analyticAt_of_differentiableOn (hN τ a i) (hB.mem_nhds hb₀)).mul
        (GlobalTheory.FrameLift.analyticAt_ratVal c' hyc ((hM y hA hyV).1 τ i a'))
  · obtain ⟨g, hg⟩ := hex _ hb₀
    obtain ⟨G, hG, -⟩ := GlobalTheory.FrameLift.exists_transport (hpt _ hb₀) (cxFrame T.Z _)
    show IsUnit (N (c'.e y) τ * (M τ).map fun r => ratVal r (c'.e.symm (c'.e y))).det
    rw [← key _ hb₀ G g hG hg τ]
    exact G.isUnit_det_co g τ
  · filter_upwards [hB.mem_nhds hb₀] with b hb
    refine ⟨hex b hb, fun hsb g hg Me τ => ?_⟩
    obtain ⟨G, hG, hGm⟩ := GlobalTheory.FrameLift.exists_transport (hpt b hb) (cxFrame T.Z _)
    rw [← key b hb G g hG hg τ, ← hGm Me τ]
    exact Me.change _ G g τ

end
