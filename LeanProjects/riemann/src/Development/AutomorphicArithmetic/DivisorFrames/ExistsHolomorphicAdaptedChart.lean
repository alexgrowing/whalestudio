import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHolAdapted
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToroidalModelChartFlag
open NumberField Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.LieHt GlobalTheory.HeightParts
open CategoryTheory AlgebraicGeometry GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo
open GlobalTheory.MatDeriv GlobalTheory.GradedNorm Matrix
open scoped ComplexOrder
open GlobalTheory.ShFam.Hor GlobalTheory.HermFrame GlobalTheory.Toroidal

open GlobalTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cartier GlobalTheory.ProjVar in

private theorem exists_chart_frames (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β) [SmoothOfRelativeDimension Dw.dim (genStr Z)] (F : Type) [Field F] [NumberField F] (e : F ≃+* c.F) (Y : FlagCpt Z e) (σ : F →+* ℂ) (y₀ : GlobalTheory.CxPts Y.Y.str σ) :
    ∃ (ch : GlobalTheory.AlgChart Y.Y.str σ Y.Y.dim) (U : Set (GlobalTheory.CxPts Y.Y.str σ)) (g : ∀ p : GlobalTheory.CxPts Y.Y.str σ, Y.FrameAt p),
      y₀ ∈ U ∧ IsOpen U ∧ U ⊆ ch.e.source ∧ (∀ p ∈ U, ∃ t t', Y.Adapted p t (g p) t') ∧
      HolFam (ch.e '' U) (fun w => (⟨Y.down (ch.e.symm w), g (ch.e.symm w)⟩ : CxFr Z (embOf e σ))) ∧
      ∀ (G : EigMet Z (embOf e σ)) (S : Set (GlobalTheory.CxPts (genStr Z) (embOf e σ))), IsOpen S →
        G.SmoothOn (manifold Z (embOf e σ)) S → ∀ τ : E →+* ℂ,
          IsPosFrame (ch.e '' (U ∩ {p | Y.down p ∈ S})) fun w => (G.gram (Y.down (ch.e.symm w)) (g (ch.e.symm w)) τ)ᵀ := by
  obtain ⟨i₀, hi₀⟩ := (Y.Y.an σ).cover y₀
  set ch := (Y.Y.an σ).chart i₀ with hch
  have hP := TrueCx.TorHolo.isHolTo_symm ch
  obtain ⟨U, t, V, φV, Fr, hU, φU, fr, A, hyU, hφV, hUV, -, hfr⟩ :=
    CurvFrames.exists_frames_nhds_spread E H Dw l Xo c O β Z F e Y σ (Var.base y₀)
  have h0U : y₀ ∈ ptsIn Y.Y.str σ U := CxPts.mem_ptsIn.2 hyU
  have hdc : Continuous (Y.down (σ := σ)) := CxPts.continuous_of_comp (m := Y.down (σ := σ)) (f := Y.π) (fun _ => rfl)
  have himg : ∀ T : Set (GlobalTheory.CxPts Y.Y.str σ), ch.e '' (ch.e.source ∩ T) = ch.e.target ∩ ch.e.symm ⁻¹' T :=
    fun T => ch.e.image_source_inter_eq' T
  have hΩ : IsOpen (ch.e.target ∩ ch.e.symm ⁻¹' ptsIn Y.Y.str σ U) := ch.e.isOpen_inter_preimage_symm (isOpen_ptsIn _)
  choose hv gsel fsel hgad hgfr hfFr hco using hfr
  classical
  let g : ∀ p : GlobalTheory.CxPts Y.Y.str σ, Y.FrameAt p := fun p =>
    if h : p ∈ ptsIn Y.Y.str σ U then gsel _ h else (Y.exists_adapted _).choose.2
  have hg : ∀ p (h : p ∈ ptsIn Y.Y.str σ U), g p = gsel _ h := fun p h => dif_pos h
  let ev' : ReciprocityTheory.L2DbarEstimates.V Y.Y.dim → (Γ(Y.Y.X, U) →+* ℂ) := fun z =>
    if h : ch.e.symm z ∈ ptsIn Y.Y.str σ U then evHom h else evHom h0U
  have hev' : ∀ z (h : ch.e.symm z ∈ ptsIn Y.Y.str σ U), ev' z = evHom h := fun z h => dif_pos h
  have hPΩ := LocLift.isHolTo_mono hP hΩ Set.inter_subset_left
  have hdev : ∀ r : Γ(Y.Y.X, U), DifferentiableOn ℂ (fun z => ev' z r)
      (ch.e.target ∩ ch.e.symm ⁻¹' ptsIn Y.Y.str σ U) := fun r z hz =>
    (HolLieFrame.differentiableAt_ev hPΩ (show Sp Γ(Y.Y.X, U) ⟶ Y.Y.X from hU.fromSpec) ev'
      (fun b hb => by rw [hev' b hb.2]; exact (Points.specMap_valMap_fromSpec hU _ hb.2).symm)
      hz r).differentiableWithinAt
  refine ⟨ch, ch.e.source ∩ ptsIn Y.Y.str σ U, g, ⟨hi₀, h0U⟩, ch.e.open_source.inter (isOpen_ptsIn _),
    Set.inter_subset_left, fun p hp => ⟨t, 1, ?_⟩, ?_, fun G S hS hG τ => ?_⟩
  · rw [hg p hp.2]; exact hgad _ _
  · rw [himg]
    refine ⟨LocLift.isHolTo_comp_hom hPΩ Y.π, fun τ i => ?_⟩
    refine HolFrames.holTan_dualMap hΩ (fr.v τ i) (fun z hz => evHom hz.2)
      (fun r => ⟨fun z => ev' z r, hdev r, fun z hz => by show _ = ev' z r; rw [hev' z hz.2]⟩) (fun z hz => ?_)
    show (g (ch.e.symm z)).v τ i = _
    rw [hg _ hz.2]
    exact hgfr _ _ τ i
  · rw [Set.inter_assoc, himg]
    have hT : IsOpen (ptsIn Y.Y.str σ U ∩ {p | Y.down p ∈ S}) := (isOpen_ptsIn _).inter (hS.preimage hdc)
    choose gf hre him hgf using fun (k k' : Fin (Dw.mult τ)) => hG V φV Fr τ k k' hφV
    let Mf : Y.Y.pts σ → Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ :=
      fun q => Matrix.of fun k k' => gf k k' (Y.down q)
    let Af : Y.Y.pts σ → Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ :=
      fun q => Matrix.of fun k k' => ev Y.Y.str σ U (A τ k k') q
    have hM : ∀ k k', (Y.Y.an σ).SmoothOn (ptsIn Y.Y.str σ U ∩ {p | Y.down p ∈ S}) (fun q => (Mf q k k').re) ∧
        (Y.Y.an σ).SmoothOn (ptsIn Y.Y.str σ U ∩ {p | Y.down p ∈ S}) (fun q => (Mf q k k').im) := fun k k' =>
      ⟨((hre k k').comp_map (hS.inter (isOpen_ptsIn _)) (m := Y.down) (f := Y.π) (fun _ => rfl)
          (Y.Y.an σ)).mono fun q hq => ⟨hq.2, hUV q hq.1⟩,
        ((him k k').comp_map (hS.inter (isOpen_ptsIn _)) (m := Y.down) (f := Y.π) (fun _ => rfl)
          (Y.Y.an σ)).mono fun q hq => ⟨hq.2, hUV q hq.1⟩⟩
    have hA : ∀ k k', (Y.Y.an σ).HoloOn (ptsIn Y.Y.str σ U ∩ {p | Y.down p ∈ S}) (fun q => Af q k k') :=
      fun k k' => AnRead.holoOn_ev_of_subset _ (fun _ hq => hq.1)
    have hsm := AnRead.smoothOn_conjTranspose_mul_mul (Y.Y.an σ) _ hT Af Mf hA hM
    have hgram : ∀ q ∈ ptsIn Y.Y.str σ U ∩ {p | Y.down p ∈ S}, G.gram (Y.down q) (g q) τ =
        (Af q)ᴴ * Mf q * Af q := by
      intro q hq'
      have hq := hq'.1
      have e1 : (fsel _ hq).co (gsel _ hq) τ = Af q := by
        rw [hco _ hq τ]; ext k k'; simp [Af, ev_eq hq]
      have e2 : G.gram (Y.down q) (fsel _ hq) τ = Mf q := by
        ext k k'; exact hgf k k' _ hq'.2 (hv _ hq) (fsel _ hq) (hfFr _ hq)
      rw [hg q hq, G.change _ (fsel _ hq) (gsel _ hq) τ, e1, e2]
    refine ⟨ch.e.isOpen_inter_preimage_symm hT, fun k k' => ?_, fun z hz => (G.pos _ _ τ).transpose⟩
    have h1 := (hsm k' k).1 i₀
    have h2 := (hsm k' k).2 i₀
    have h3 := (Complex.ofRealCLM.contDiff.comp_contDiffOn h1).add
      ((Complex.ofRealCLM.contDiff.comp_contDiffOn h2).mul (contDiffOn_const (c := Complex.I)))
    refine h3.congr fun z hz => ?_
    rw [Matrix.transpose_apply, hgram _ hz.2]
    simp only [Function.comp_apply, Complex.ofRealCLM_apply]
    exact (Complex.re_add_im _).symm

theorem UpperTheory.exists_holomorphic_adapted_chart :
    OnCore fun D O x P => ∀ (c : O.s.Comp) (σ : D.what₂.LL →+* ℂ) (y₀ : GlobalTheory.CxPts (O.var c).str σ),
      ∃ (ch : GlobalTheory.AlgChart (O.var c).str σ (O.var c).dim) (U : Set (GlobalTheory.CxPts (O.var c).str σ)) (g : ∀ p : GlobalTheory.CxPts (O.var c).str σ, (O.Φ.C c).FrameAt p),
        y₀ ∈ U ∧ GlobalTheory.BdGram.IsHolAdapted O ch U g := by
  have key : ∀ (D : D7) (O : Setup D) (c : O.s.Comp) (σ : D.what₂.LL →+* ℂ) (y₀ : GlobalTheory.CxPts (O.var c).str σ),
      ∃ (ch : GlobalTheory.AlgChart (O.var c).str σ (O.var c).dim) (U : Set (GlobalTheory.CxPts (O.var c).str σ)) (g : ∀ p : GlobalTheory.CxPts (O.var c).str σ, (O.Φ.C c).FrameAt p),
        y₀ ∈ U ∧ GlobalTheory.BdGram.IsHolAdapted O ch U g := by
    intro D O c σ y₀
    obtain ⟨ch, U, g, h0, h1, h2, h3, h4, h5⟩ := exists_chart_frames _ _ _ _ _ _ _ _ _ _ _ (O.Φ.C c) σ y₀
    refine ⟨ch, U, g, h0, h1, h2, h1.inter ?_, h3, h4, h5⟩
    exact (isOpen_not_liesIn (genBd O.s.T.Z)).preimage
      (GlobalTheory.CxPts.continuous_of_comp (m := (O.Φ.C c).down (σ := σ)) (f := (O.Φ.C c).π) (fun _ => rfl))
  unfold OnCore
  intros
  apply key
