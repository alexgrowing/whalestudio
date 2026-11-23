import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLieBase
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgePeriodGram
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeChartBoundsOfSchurLemW
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineEigenframeNearPoint
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousOnFrameDirectionsInverse
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrameCoordinatesEqRationalMatrixValuesChartStatement
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LieBase.ChartFrames

open GlobalTheory GlobalTheory.LieMet GlobalTheory.Cartier in

theorem exists_frameFam {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} (Z : Model Xo c β) (σ : c.F →+* ℂ)
    {n g : ℕ} {e : OpenPartialHomeomorph (CxPts (genStr Z) σ) (Fin n → ℂ)} {ex : ExpMaps Z σ g} (hex : IsExpChart e ex)
    (y₀ : CxPts (genStr Z) σ) (hy₀ : y₀ ∈ e.source) :
    ∃ (V : (gen Z).affineOpens) (φ : c.F →+* Γ(gen Z, V.1)) (F : EigFrame Z φ (LogKS.chart V ≫ genι Z))
      (B : Set (Fin n → ℂ)) (a : (Fin n → ℂ) → CxFr Z σ), LogKS.chart V ≫ genStr Z = spMap φ ∧ IsOpen B ∧ e y₀ ∈ B ∧
      B ⊆ e.target ∧ HolFam B a ∧
      ∀ b ∈ B, (a b).1 = e.symm b ∧ ∃ hy : (a b).1 ∈ ptsIn (genStr Z) σ V.1, F.IsMap (evHom hy) (a b).2 := by
  obtain ⟨U, hU, φ, F, hzU, hφ, -⟩ :=
    EigSpread.exists_stable_eigFrame E H Dw l Xo c O β Z (y₀.1 (IsLocalRing.closedPoint ℂ))
  let V : (gen Z).affineOpens := ⟨U, hU⟩
  have hφ' : LogKS.chart V ≫ genStr Z = spMap φ := hφ
  have hy₀V : y₀ ∈ ptsIn (genStr Z) σ V.1 := CxPts.mem_ptsIn.2 hzU
  have hov : ∀ (y : CxPts (genStr Z) σ) (hy : y ∈ ptsIn (genStr Z) σ V.1), σ = (evHom hy).comp φ := fun y hy =>
    EigLoc.spMap_inj (y.2.symm.trans (by
      rw [← ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp_spMap, ← hφ', ← Category.assoc, spMap_evHom hy]))
  have hx : ∀ (y : CxPts (genStr Z) σ) (hy : y ∈ ptsIn (genStr Z) σ V.1),
      y.1 ≫ genι Z = spMap (evHom hy) ≫ LogKS.chart V ≫ genι Z := fun y hy => by
    rw [← Category.assoc, spMap_evHom hy]
  have hfr : ∀ (y : CxPts (genStr Z) σ) (hy : y ∈ ptsIn (genStr Z) σ V.1),
      ∃ f : EigFrame Z σ (y.1 ≫ genι Z), EigFrame.IsMap (F : EigFrame Z φ (LogKS.chart V ≫ genι Z)) (evHom hy) f :=
    fun y hy => EigFrame.exists_isMap F (evHom hy) (hov y hy) (hx y hy)
  choose fr hfr using hfr
  have h0 : e.symm (e y₀) ∈ ptsIn (genStr Z) σ V.1 := by rw [e.left_inv hy₀]; exact hy₀V
  let a : (Fin n → ℂ) → CxFr Z σ := fun b =>
    if h : e.symm b ∈ ptsIn (genStr Z) σ V.1 then ⟨e.symm b, fr _ h⟩ else ⟨e.symm (e y₀), fr _ h0⟩
  have ha : ∀ b (h : e.symm b ∈ ptsIn (genStr Z) σ V.1), a b = ⟨e.symm b, fr _ h⟩ := fun b h => dif_pos h
  let B : Set (Fin n → ℂ) := e.target ∩ e.symm ⁻¹' ptsIn (genStr Z) σ V.1
  have hB : IsOpen B := e.continuousOn_symm.isOpen_inter_preimage e.open_target (isOpen_ptsIn _)
  have hBt : B ⊆ e.target := Set.inter_subset_left
  have hyB : IsHolTo B (fun b => (e.symm b).1) := LocLift.isHolTo_mono hex.2.2.1 hB hBt
  let ev : (Fin n → ℂ) → (Γ(gen Z, V.1) →+* ℂ) := fun b =>
    if h : e.symm b ∈ ptsIn (genStr Z) σ V.1 then evHom h else evHom h0
  have hev : ∀ b (h : e.symm b ∈ ptsIn (genStr Z) σ V.1), ev b = evHom h := fun b h => dif_pos h
  have : IsOpenImmersion (LogKS.chart V) := IsAffineOpen.isOpenImmersion_fromSpec V.2
  have hd : ∀ r : Γ(gen Z, V.1), DifferentiableOn ℂ (fun b => ev b r) B := fun r b hb =>
    (HolLieFrame.differentiableAt_ev hyB (LogKS.chart V) ev
      (fun b' hb' => by rw [hev b' hb'.2]; exact (spMap_evHom hb'.2).symm) hb r).differentiableWithinAt
  refine ⟨V, φ, F, B, a, hφ', hB, ⟨e.map_source hy₀, h0⟩, hBt, ⟨?_, fun ρ i => ?_⟩, fun b hb => ?_⟩
  · exact LocLift.isHolTo_congr hyB fun b hb => by rw [ha b hb.2]
  · exact HolFrames.holTan_dualMap hB (F.v ρ i) (fun b hb => evHom hb.2)
      (fun r => ⟨fun b => ev b r, hd r, fun b hb => (RingHom.congr_fun (hev b hb.2) r).symm⟩)
      (fun b hb => by rw [ha b hb.2]; exact hfr _ hb.2 ρ i)
  · rw [ha b hb.2]
    exact ⟨rfl, hb.2, hfr _ hb.2⟩

open GlobalTheory.Cartier in

theorem exists_open_mem {F : Type} [Field F] (X : Var F) {κ : Type} [Finite κ] {m : κ → ℕ} (S : Fr (ratOf X) m 0)
    {p : X.X} {A : Mat m X.Fn} (hA : A ∈ S.S p) : ∃ G : X.X.Opens, p ∈ G ∧ ∀ p' ∈ G, A ∈ S.S p' := by
  obtain ⟨U, B, hU, hB, hS⟩ := S.loc p
  have hP := (hS _ hU A).1 hA
  have hreg : ∀ g : X.Fn, RegAt p g → ∃ W : X.X.Opens, p ∈ W ∧ ∀ p' ∈ W, RegAt p' g := by
    intro g hg
    obtain ⟨W, hW, a, rfl⟩ := hg.exists_fnOf
    exact ⟨W, hW, fun p' hp' => regAt_fnOf hp' _ a⟩
  choose W hW hW' using fun (τ : κ) (i j : Fin (m τ)) => hreg _ (mem_O_ratOf.1 ((hP τ).1 i j))
  choose W₂ hW₂ hW₂' using fun τ : κ => hreg _ (mem_O_ratOf.1 (hP τ).2.2.1)
  let G : Set X.X := ((show X.X.Opens from U) : Set X.X) ∩ (⋂ τ, ⋂ i, ⋂ j, (W τ i j : Set X.X)) ∩ ⋂ τ, (W₂ τ : Set X.X)
  have hG : IsOpen G := (U.isOpen.inter (isOpen_iInter_of_finite fun τ => isOpen_iInter_of_finite fun i =>
    isOpen_iInter_of_finite fun j => (W τ i j).isOpen)).inter (isOpen_iInter_of_finite fun τ => (W₂ τ).isOpen)
  refine ⟨⟨G, hG⟩, ⟨⟨hU, Set.mem_iInter.2 fun τ => Set.mem_iInter.2 fun i => Set.mem_iInter.2 fun j => hW τ i j⟩,
    Set.mem_iInter.2 fun τ => hW₂ τ⟩, fun p' hp' => ?_⟩
  obtain ⟨⟨h1, h2⟩, h3⟩ := hp'
  exact (hS _ h1 A).2 fun τ => ⟨fun i j => mem_O_ratOf.2 (hW' τ i j p'
      (Set.mem_iInter.1 (Set.mem_iInter.1 (Set.mem_iInter.1 h2 τ) i) j)), (hP τ).2.1,
    mem_O_ratOf.2 (hW₂' τ p' (Set.mem_iInter.1 h3 τ)), fun i j hi => absurd hi (by simp)⟩

theorem valR_appIso_inv {Y X : Scheme.{0}} (j : Y ⟶ X) [IsOpenImmersion j] (W : Y.Opens) (g : Γ(Y, W))
    (w : Sp ℂ ⟶ Y) (hw : ⊤ ≤ w ⁻¹ᵁ W) :
    valR (w ≫ j) (j ''ᵁ W) ((j.appIso W).inv.hom g) = valR w W g := by
  have hle : W ≤ j ⁻¹ᵁ j ''ᵁ W := (j.preimage_image_eq W).ge
  rw [← GlobalTheory.Points.valR_appLE w j hle hw, ← CommRingCat.comp_apply, Scheme.Hom.appIso_inv_appLE]
  exact GlobalTheory.Points.valR_res w le_rfl hw g

end GlobalTheory.LieBase.ChartFrames

namespace GlobalTheory.LieBase.ChartFrames

open GlobalTheory GlobalTheory.LieMet GlobalTheory.Cartier

theorem cxOf_mem_image {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β} {F : Type} [Field F]
    (e : F ≃+* c.F) (σ : c.F →+* ℂ) {X : Var F} {j : X.X ⟶ gen Z} [IsOpenImmersion j]
    (hj : j ≫ genStr Z ≫ spMap e.toRingHom = X.str) (W : X.X.Opens) (z : CxPts X.str (σ.comp e.toRingHom)) :
    cxOf e σ hj z ∈ ptsIn (genStr Z) σ (j ''ᵁ W) ↔ z ∈ ptsIn X.str (σ.comp e.toRingHom) W := by
  rw [CxPts.mem_ptsIn, CxPts.mem_ptsIn]
  show j (z.1 (IsLocalRing.closedPoint ℂ)) ∈ j ''ᵁ W ↔ _
  exact ⟨fun ⟨x, hx, hxe⟩ => (j.isOpenEmbedding.injective hxe) ▸ hx, fun h => ⟨_, h, rfl⟩⟩

end GlobalTheory.LieBase.ChartFrames

open GlobalTheory GlobalTheory.LieMet GlobalTheory.Cartier GlobalTheory.LieBase.ChartFrames in

theorem GlobalTheory.LieBase.exists_chart_dirs : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (C : FlagCpt T.Z e) (X : Var F) (j : X.X ⟶ gen T.Z) (f : C.Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e C X j f f₀ Eb A₀ → ∀ (y : GlobalTheory.CxPts X.str (σ.comp e.toRingHom)) (n g : ℕ) (ch₀ : OpenPartialHomeomorph (GlobalTheory.CxPts (genStr T.Z) σ) (Fin n → ℂ)) (ex : ExpMaps T.Z σ g), IsExpChart ch₀ ex → cxOf e σ hj y ∈ ch₀.source → ch₀ (cxOf e σ hj y) = 0 → ∃ A ∈ Eb.S (GlobalTheory.Cartier.under y), ∃ r : ℝ, 0 < r ∧ ∃ W : (Fin n → ℂ) → (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) → Fin g → ℂ, (∀ p k, DifferentiableOn ℂ (fun u => W u p k) (Metric.ball 0 r)) ∧ LinearIndependent ℂ (W 0) ∧ ∀ z : GlobalTheory.CxPts X.str (σ.comp e.toRingHom), cxOf e σ hj z ∈ ch₀.source → ch₀ (cxOf e σ hj z) ∈ Metric.ball 0 r → (∃ g' : EigFrame T.Z σ ((cxOf e σ hj z).1 ≫ genι T.Z), FrameAt e f₀ A₀ A z g') ∧ ∀ g' : EigFrame T.Z σ ((cxOf e σ hj z).1 ≫ genι T.Z), FrameAt e f₀ A₀ A z g' → Dirs ⟨cxOf e σ hj z, g'⟩ (fun w => (ex (cxOf e σ hj z) w).left) (W (ch₀ (cxOf e σ hj z))) := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ C X j f f₀ Eb A₀ hj hL y n g ch₀ ex hex hys hy0
  obtain ⟨hoi, -, hT⟩ := hL
  obtain ⟨A, hA⟩ := Eb.nonempty (GlobalTheory.Cartier.under y)
  obtain ⟨V, φ, Φ, B, a, hφ, hB, h0B, hBt, ha, hab⟩ := exists_frameFam T.Z σ hex (cxOf e σ hj y) hys
  rw [hy0] at h0B
  have hsy : ch₀.symm 0 = cxOf e σ hj y := by rw [← hy0]; exact ch₀.left_inv hys
  have hyV : cxOf e σ hj y ∈ ptsIn (genStr T.Z) σ V.1 := by
    obtain ⟨h1, hy, -⟩ := hab 0 h0B
    rwa [h1, hsy] at hy
  obtain ⟨M, hM⟩ := GlobalTheory.T.frame_coordinates_eq_rational_matrix_values_chart E H Dw l Xo c O β T.Z σ F e X j f₀ Eb A₀ hj hoi hT V φ Φ hφ A
  have hMy := hM y hA hyV
  choose Ws hWs s hs using fun τ p q => (hMy.1 τ p q).exists_fnOf
  obtain ⟨G, hG, hGA⟩ := exists_open_mem X Eb hA

  have hoi' : IsOpenImmersion j := hoi
  let sv : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Fin (Dw.mult τ) → (Fin n → ℂ) → ℂ := fun τ p q u =>
    valAt' (ch₀.symm u).1 (j ''ᵁ Ws τ p q) ((j.appIso (Ws τ p q)).inv.hom (s τ p q))
  let Ω : Set (Fin n → ℂ) := B ∩ (ch₀.target ∩ ch₀.symm ⁻¹' (ptsIn (genStr T.Z) σ (j ''ᵁ G) ∩
    ⋂ τ, ⋂ p, ⋂ q, ptsIn (genStr T.Z) σ (j ''ᵁ Ws τ p q)))
  have hΩ : IsOpen Ω := hB.inter (ch₀.continuousOn_symm.isOpen_inter_preimage ch₀.open_target
    ((isOpen_ptsIn _).inter (isOpen_iInter_of_finite fun τ => isOpen_iInter_of_finite fun p =>
      isOpen_iInter_of_finite fun q => isOpen_ptsIn _)))
  have h0Ω : (0 : Fin n → ℂ) ∈ Ω := by
    refine ⟨h0B, hBt h0B, ?_⟩
    rw [Set.mem_preimage, hsy]
    exact ⟨(cxOf_mem_image e σ hj G y).2 (CxPts.mem_ptsIn.2 hG), Set.mem_iInter.2 fun τ => Set.mem_iInter.2 fun p =>
      Set.mem_iInter.2 fun q => (cxOf_mem_image e σ hj _ y).2 (CxPts.mem_ptsIn.2 (hWs τ p q))⟩
  obtain ⟨r, hr, hrΩ⟩ := Metric.isOpen_iff.1 hΩ 0 h0Ω
  have src : ∀ b ∈ B, (a b).1 ∈ ch₀.source := fun b hb => by
    rw [(hab b hb).1]; exact ch₀.map_target (hBt hb)
  have h5 := fun b (hb : b ∈ B) => hex.2.2.2.2.2 _ (src b hb)
  choose! Wa hWa using fun b (hb : b ∈ B) (z : Pad.Letter Dw) => ((h5 b hb).2 _ ((a b).2.tan z.1 z.2)).exists
  have hWad : ∀ b ∈ B, ∀ z, DifferentiableAt ℂ (fun b => Wa b z) b := fun b hb z =>
    ExpDirs.differentiableAt_dir hex hB ha.1 src (ha.2 z.1 z.2) (fun b hb => hWa b hb z) hb
  have hsvd : ∀ τ p q, ∀ u ∈ Ω, DifferentiableAt ℂ (sv τ p q) u := fun τ p q u hu => by
    have h := hex.2.2.1 (j ''ᵁ Ws τ p q) ((j.appIso (Ws τ p q)).inv.hom (s τ p q))
    refine h.2.differentiableAt (h.1.mem_nhds ⟨hu.2.1, ?_⟩)
    exact Set.mem_iInter.1 (Set.mem_iInter.1 (Set.mem_iInter.1 hu.2.2.2 τ) p) q
  let W : (Fin n → ℂ) → (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) → Fin g → ℂ := fun u p k =>
    ∑ q, sv p.1 q p.2 u * Wa u ⟨p.1, q⟩ k
  have evEq : ∀ {y₁ y₂ : CxPts (genStr T.Z) σ} (h₁ : y₁ ∈ ptsIn (genStr T.Z) σ V.1)
      (h₂ : y₂ ∈ ptsIn (genStr T.Z) σ V.1), y₁ = y₂ → evHom h₁ = evHom h₂ := by
    rintro _ _ _ _ rfl; rfl
  have key : ∀ z : CxPts X.str (σ.comp e.toRingHom), cxOf e σ hj z ∈ ch₀.source →
      ch₀ (cxOf e σ hj z) ∈ Metric.ball 0 r →
      (∃ g' : EigFrame T.Z σ ((cxOf e σ hj z).1 ≫ genι T.Z), FrameAt e f₀ A₀ A z g') ∧
      ∀ g' : EigFrame T.Z σ ((cxOf e σ hj z).1 ≫ genι T.Z), FrameAt e f₀ A₀ A z g' →
        Dirs ⟨cxOf e σ hj z, g'⟩ (fun w => (ex (cxOf e σ hj z) w).left) (W (ch₀ (cxOf e σ hj z))) := by
    intro z hzs hzr
    have huΩ := hrΩ hzr
    have hsymm : ch₀.symm (ch₀ (cxOf e σ hj z)) = cxOf e σ hj z := ch₀.left_inv hzs
    obtain ⟨huB, -, hu1, hu2⟩ := huΩ
    rw [hsymm] at hu1 hu2
    have hzG := (cxOf_mem_image e σ hj G z).1 hu1
    have hzW : ∀ τ p q, z ∈ ptsIn X.str (σ.comp e.toRingHom) (Ws τ p q) := fun τ p q =>
      (cxOf_mem_image e σ hj _ z).1 (Set.mem_iInter.1 (Set.mem_iInter.1 (Set.mem_iInter.1 hu2 τ) p) q)
    have hAz : A ∈ Eb.S (GlobalTheory.Cartier.under z) := hGA _ (CxPts.mem_ptsIn.1 hzG)
    obtain ⟨ha1, hyV', hmap⟩ := hab _ huB
    have hzV : cxOf e σ hj z ∈ ptsIn (genStr T.Z) σ V.1 := by rw [← hsymm, ← ha1]; exact hyV'
    obtain ⟨-, hex', hco⟩ := hM z hAz hzV
    refine ⟨hex', fun g' hg' => ?_⟩
    have hov : σ = (evHom hzV).comp φ := EigLoc.spMap_inj ((cxOf e σ hj z).2.symm.trans (by
      rw [← ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp_spMap, ← hφ, ← Category.assoc, spMap_evHom hzV]))
    have hx : (cxOf e σ hj z).1 ≫ genι T.Z = spMap (evHom hzV) ≫ LogKS.chart V ≫ genι T.Z := by
      rw [← Category.assoc, spMap_evHom hzV]
    obtain ⟨fr, hfr⟩ := Φ.exists_isMap (evHom hzV) hov hx
    have hcoM := hco g' hg' fr hfr
    have hpt : (a (ch₀ (cxOf e σ hj z))).1 = cxOf e σ hj z := ha1.trans hsymm
    have hvq : ∀ τ i, fr.v τ i = (a (ch₀ (cxOf e σ hj z))).2.v τ i := fun τ i => by
      rw [hfr τ i, hmap τ i, evEq hzV hyV' hpt.symm]
    have hD : ∀ q : Pad.Letter Dw, IsDerivAt0 (fun w => (ex (cxOf e σ hj z) w).left)
        (Wa (ch₀ (cxOf e σ hj z)) q) (fr.v q.1 q.2) := fun q => by
      have tr : ∀ (x x' : CxPts (genStr T.Z) σ), x = x' → ∀ w v,
          IsDerivAt0 (fun u => (ex x u).left) w v → IsDerivAt0 (fun u => (ex x' u).left) w v := by
        rintro _ _ rfl _ _ h; exact h
      rw [hvq]
      exact tr _ _ hpt _ _ (hWa _ huB q)
    have e0 : ex (cxOf e σ hj z) 0 = 1 := by simpa using hex.2.2.2.1 _ hzs 0 0
    rintro ⟨τ, i⟩
    have hcomb := ExpDirs.isDerivAt0_of_comb (congrArg (·.left) e0) (fun k => fr.tan τ k) (fun k => hD ⟨τ, k⟩)
      (g'.tan τ i) (fr.co_spec g' τ i)
    convert hcomb using 1
    funext k
    simp only [W, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun q _ => ?_
    congr 1
    rw [hcoM τ, Matrix.map_apply, ← hs τ q i, ratVal_fnOf (hzW τ q i)]
    show valR (ch₀.symm (ch₀ (cxOf e σ hj z))).1 _ _ = _
    rw [hsymm]
    exact valR_appIso_inv j _ _ z.1 (hzW τ q i)
  refine ⟨A, hA, r, hr, W, fun p k u hu => ?_, ?_, key⟩
  · have huΩ := hrΩ hu
    refine DifferentiableAt.differentiableWithinAt ?_
    simp only [W]
    refine DifferentiableAt.fun_sum fun q _ => (hsvd _ _ _ u huΩ).mul ?_
    exact differentiableAt_pi.1 (hWad u huΩ.1 ⟨p.1, q⟩) k
  · obtain ⟨⟨g', hg'⟩, hall⟩ := key y hys (by rw [hy0]; exact Metric.mem_ball_self hr)
    have hD := hall g' hg'
    rw [hy0] at hD
    have e0 : ex (cxOf e σ hj y) 0 = 1 := by simpa using hex.2.2.2.1 _ hys 0 0
    have h5y := hex.2.2.2.2.2 _ hys
    obtain ⟨bs, hbs⟩ := ExpDirs.dirs_basis g' (e := fun w => (ex (cxOf e σ hj y) w).left) (congrArg (·.left) e0)
      h5y.1 h5y.2 hD
    rw [← hbs]
    exact bs.linearIndependent
