import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelGramPosSemidef
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalFlagCoordinates
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsHolToOfOpenImmersion
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsHolomorphicLieFrame
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLinearEquivLift
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsDifferentiableOnTransfer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsConjFsBasisOfUnitary
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjugateHermitianSmooth
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAlgAtlasAtlasOf
import Development.AbelianVarietyTheory.Definitions.Divisors.ExtFormAdjEqNegSecondForm

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open CategoryTheory AlgebraicGeometry TopologicalSpace Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R.FinalTheorems GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Hor GlobalTheory.CurvInterp
open scoped ComplexOrder
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ShFam.CurvFrames

open scoped ContDiff Topology

section Charts

variable {F : Type} [Field F] {Y : Var F} {d : ℕ} {M : Man d}

theorem isHolTo_pt_symm (I : ManIs M Y) (a : Fin (M.n + 1)) (ψ : OpenPartialHomeomorph (M.X a) (Fin d → ℂ))
    (hψ : IsCompatChart (M.A a) ψ) : IsHolTo ψ.target fun z => (I.pt a (ψ.symm z)).1 := by
  refine HolPeriods.isHolTo_of_local fun z hz => ?_
  obtain ⟨j, hj⟩ := (M.A a).cover (ψ.symm z)
  obtain ⟨c, hc⟩ := I.alg a j
  have hB : IsOpen (ψ.target ∩ ψ.symm ⁻¹' ((M.A a).chart j).source) :=
    ψ.isOpen_inter_preimage_symm ((M.A a).chart j).open_source
  refine ⟨ψ.target ∩ ψ.symm ⁻¹' ((M.A a).chart j).source, ⟨hz, hj⟩, Set.inter_subset_left, ?_⟩
  have hT : DifferentiableOn ℂ ((M.A a).chart j ∘ ψ.symm) (ψ.target ∩ ψ.symm ⁻¹' ((M.A a).chart j).source) :=
    fun w hw => ((hψ j).2 w hw).differentiableAt.differentiableWithinAt
  have h1 := LocLift.isHolTo_comp (TrueCx.TorHolo.isHolTo_symm c) hB
    (β := fun w => (EuclideanSpace.equiv (Fin d) ℂ).symm (((M.A a).chart j ∘ ψ.symm) w))
    ((EuclideanSpace.equiv (Fin d) ℂ).symm.differentiable.comp_differentiableOn hT) (fun w hw => by
      have h2 := ((M.A a).chart j).map_source hw.2
      rw [hc, Homeomorph.transOpenPartialHomeomorph_target] at h2
      simp only [Function.comp_apply]
      rw [hc]
      exact h2)
  refine LocLift.isHolTo_congr h1 fun w hw => ?_
  have hs : I.pt a (ψ.symm w) ∈ c.e.source := by
    have h4 := hw.2
    rw [hc] at h4
    exact h4
  simp only [Function.comp_apply]
  rw [hc]
  show _ = (c.e.symm ((EuclideanSpace.equiv (Fin d) ℂ).symm ((EuclideanSpace.equiv (Fin d) ℂ) (c.e (I.pt a (ψ.symm w)))))).1
  rw [ContinuousLinearEquiv.symm_apply_apply, c.e.left_inv hs]

theorem contDiffOn_comp_pt_symm (I : ManIs M Y) (a : Fin (M.n + 1)) (ψ : OpenPartialHomeomorph (M.X a) (Fin d → ℂ))
    (hψ : IsCompatChart (M.A a) ψ) {D : ℕ} (R : AnRead Y.str (I.ε a) D) {S : Set (Pts Y (I.ε a))} (hS : IsOpen S)
    {f : Pts Y (I.ε a) → ℝ} (hf : R.SmoothOn S f) :
    ContDiffOn ℝ ∞ (fun z => f (I.pt a (ψ.symm z))) (ψ.target ∩ (fun z => I.pt a (ψ.symm z)) ⁻¹' S) := by
  have hP := isHolTo_pt_symm I a ψ hψ
  have hPc : ContinuousOn (fun z => I.pt a (ψ.symm z)) ψ.target :=
    (I.pt a).continuous.comp_continuousOn ψ.continuousOn_symm
  intro z hz
  obtain ⟨i, hi⟩ := R.cover (I.pt a (ψ.symm z))
  have hB0 : IsOpen (ψ.target ∩ (fun z => I.pt a (ψ.symm z)) ⁻¹' (S ∩ (R.chart i).e.source)) :=
    hPc.isOpen_inter_preimage ψ.open_target (hS.inter (R.chart i).e.open_source)
  have hz0 : z ∈ ψ.target ∩ (fun z => I.pt a (ψ.symm z)) ⁻¹' (S ∩ (R.chart i).e.source) := ⟨hz.1, hz.2, hi⟩
  have hd : DifferentiableOn ℂ (fun v => (R.chart i).e (I.pt a (ψ.symm v)))
      (ψ.target ∩ (fun z => I.pt a (ψ.symm z)) ⁻¹' (S ∩ (R.chart i).e.source)) := fun w hw =>
    (TrueCx.TorHolo.differentiableAt_chart ψ.open_target hP (R.chart i) hw.1 hw.2.2).differentiableWithinAt
  have h1 : ContDiffAt ℝ ∞ (fun v => (R.chart i).e (I.pt a (ψ.symm v))) z :=
    ((SCV.analyticOnNhd_of_differentiableOn hB0 hd z hz0).contDiffAt (n := ∞)).restrict_scalars ℝ
  have hO : IsOpen ((R.chart i).e.target ∩ (R.chart i).e.symm ⁻¹' S) := (R.chart i).e.isOpen_inter_preimage_symm hS
  have h2 : ContDiffAt ℝ ∞ (f ∘ (R.chart i).e.symm) ((R.chart i).e (I.pt a (ψ.symm z))) :=
    (hf i).contDiffAt (hO.mem_nhds ⟨(R.chart i).e.map_source hi, by
      rw [Set.mem_preimage, (R.chart i).e.left_inv hi]; exact hz.2⟩)
  refine ((h2.comp z h1).congr_of_eventuallyEq ?_).contDiffWithinAt
  filter_upwards [hB0.mem_nhds hz0] with w hw
  simp only [Function.comp_apply, (R.chart i).e.left_inv hw.2.2]

end Charts

section Frames

open Limits GlobalTheory.ShFam.Pad

attribute [local instance] Over.cartesianMonoidalCategory

theorem exists_frames_nhds_spread : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β) (F : Type) [Field F] [NumberField F] (e : F ≃+* c.F) (Y : FlagCpt Z e) (σ : F →+* ℂ) (y : Y.Y.X), ∃ (U : Y.Y.X.Opens) (t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Y.Y.Fnˣ) (V : (gen Z).affineOpens) (φ : c.F →+* Γ(gen Z, V.1)) (Fr : EigFrame Z φ (LogKS.chart V ≫ genι Z)) (hU : IsAffineOpen U) (φU : c.F →+* Γ(Y.Y.X, U)) (fr : EigFrame Z φU (((show Sp Γ(Y.Y.X, U) ⟶ Y.Y.X from hU.fromSpec) ≫ Y.π) ≫ genι Z)) (A : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) Γ(Y.Y.X, U)), y ∈ U ∧ LogKS.chart V ≫ genStr Z = spMap φ ∧ (∀ p : Y.Y.pts σ, p ∈ ptsIn Y.Y.str σ U → Y.down p ∈ ptsIn (genStr Z) (embOf e σ) V.1) ∧ (∀ y' ∈ U, ∀ τ i, (Y.gr τ i).IsEqn y' (t τ i)) ∧ ∀ (p : Y.Y.pts σ) (hp : p ∈ ptsIn Y.Y.str σ U), ∃ (hv : Y.down p ∈ ptsIn (genStr Z) (embOf e σ) V.1) (g f : Y.FrameAt p), Y.Adapted p t g 1 ∧ fr.IsMap (evHom hp) g ∧ Fr.IsMap (evHom hv) f ∧ ∀ τ, f.co g τ = (A τ).map (evHom hp) := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ _ e Y σ y
  obtain ⟨V₀, hV₀, φ₀, Fr₀, hy₀, hs₀, -⟩ := EigSpread.exists_stable_eigFrame E H Dw l Xo c O β Z (Y.π y)
  obtain ⟨U, hU, hy, φ, fr, t, hle, hs, hT, ht⟩ := Spread.exists_frame_nhds E H Dw l Xo c O β Z F e Y y (Y.π ⁻¹ᵁ V₀) hy₀
  let ρ : Γ(gen Z, V₀) →+* Γ(Y.Y.X, U) := (Y.π.appLE V₀ U hle).hom
  have hρ : spMap ρ ≫ (show Sp Γ(gen Z, V₀) ⟶ gen Z from hV₀.fromSpec) =
      (show Sp Γ(Y.Y.X, U) ⟶ Y.Y.X from hU.fromSpec) ≫ Y.π := IsAffineOpen.SpecMap_appLE_fromSpec Y.π hV₀ hU hle

  have hφ : φ = ρ.comp φ₀ := EigLoc.spMap_inj (by
    rw [← hs, ← hρ, Category.assoc, hs₀]
    exact spMap_comp_spMap φ₀ ρ)
  have hxρ : ((show Sp Γ(Y.Y.X, U) ⟶ Y.Y.X from hU.fromSpec) ≫ Y.π) ≫ genι Z =
      spMap ρ ≫ (show Sp Γ(gen Z, V₀) ⟶ gen Z from hV₀.fromSpec) ≫ genι Z := by
    rw [← Category.assoc, hρ]
  obtain ⟨Fr', hFr'⟩ := Fr₀.exists_isMap ρ hφ hxρ
  have hdown : ∀ p : Y.Y.pts σ, p ∈ ptsIn Y.Y.str σ U → Y.down p ∈ ptsIn (genStr Z) (embOf e σ) V₀ := fun p hp =>
    CxPts.mem_ptsIn.2 (hle (CxPts.mem_ptsIn.1 hp))
  refine ⟨U, t, ⟨V₀, hV₀⟩, φ₀, Fr₀, hU, φ, fr, fun τ => Fr'.co fr τ, hy, hs₀, hdown, ht, fun p hp => ⟨hdown p hp, ?_⟩⟩
  have hv := hdown p hp
  have hpU : spMap (evHom hp) ≫ (show Sp Γ(Y.Y.X, U) ⟶ Y.Y.X from hU.fromSpec) = p.1 :=
    Points.specMap_valMap_fromSpec hU p.1 hp
  have hpV : spMap (evHom hv) ≫ (show Sp Γ(gen Z, V₀) ⟶ gen Z from hV₀.fromSpec) = (Y.down p).1 :=
    Points.specMap_valMap_fromSpec hV₀ (Y.down p).1 hv
  have hov : (Y.down p).1 ≫ genStr Z = spMap (embOf e σ) := (Y.down p).2
  have hxg : (Y.down p).1 ≫ genι Z = spMap (evHom hp) ≫ ((show Sp Γ(Y.Y.X, U) ⟶ Y.Y.X from hU.fromSpec) ≫ Y.π) ≫ genι Z := by
    rw [← Category.assoc, ← Category.assoc, hpU]; rfl
  have hxf : (Y.down p).1 ≫ genι Z = spMap (evHom hv) ≫ (show Sp Γ(gen Z, V₀) ⟶ gen Z from hV₀.fromSpec) ≫ genι Z := by
    rw [← Category.assoc, hpV]
  have hφg : embOf e σ = (evHom hp).comp φ := EigLoc.spMap_inj (hov.symm.trans (by
    rw [← spMap_comp_spMap φ (evHom hp), ← hs, ← Category.assoc, ← Category.assoc, hpU]; rfl))
  have hφf : embOf e σ = (evHom hv).comp φ₀ := EigLoc.spMap_inj (hov.symm.trans (by
    rw [← spMap_comp_spMap φ₀ (evHom hv), ← hs₀, ← Category.assoc, hpV]))
  have hev : (evHom hp).comp ρ = evHom hv := EigLoc.spMap_inj ((cancel_mono
    (show Sp Γ(gen Z, V₀) ⟶ gen Z from hV₀.fromSpec)).1 (by
      rw [hpV, ← spMap_comp_spMap ρ (evHom hp), Category.assoc, hρ, ← Category.assoc, hpU]; rfl))
  obtain ⟨g, hg⟩ := fr.exists_isMap (evHom hp) hφg hxg
  obtain ⟨f, hf⟩ := Fr₀.exists_isMap (evHom hv) hφf hxf
  have hf' : Fr'.IsMap (evHom hp) f := fun τ i => by
    rw [hf τ i, hFr' τ i, GradedPieces.dual_comp, hev]
  refine ⟨g, f, ?_, hg, hf, fun τ => EigFrame.IsMap.co τ hf' hg hxg⟩
  have hb : Var.base p ∈ U := CxPts.mem_ptsIn.1 hp
  let gm : Γ(Y.Y.X, U) →+* Y.Y.X.presheaf.stalk (Var.base p) := (Y.Y.X.presheaf.germ U (Var.base p) hb).hom
  have hxs : stalkPt Y.Y (Var.base p) ≫ Y.π ≫ genι Z =
      spMap gm ≫ ((show Sp Γ(Y.Y.X, U) ⟶ Y.Y.X from hU.fromSpec) ≫ Y.π) ≫ genι Z := by
    have h0 : stalkPt Y.Y (Var.base p) = spMap gm ≫ (show Sp Γ(Y.Y.X, U) ⟶ Y.Y.X from hU.fromSpec) :=
      (Spread.spMap_germ hU hb).symm
    rw [h0]; simp only [Category.assoc]
  obtain ⟨frs, hfrs⟩ := fr.exists_isMap gm rfl hxs
  have hgm : (Var.evStalk p).comp gm = evHom hp :=
    (congrArg CommRingCat.Hom.hom (HolFrames.valR_eq_germ p.1 U hp)).symm
  have hgs : frs.IsMap (Var.evStalk p) g := fun τ i => by
    rw [hg τ i, hfrs τ i, GradedPieces.dual_comp, hgm]
  have hxp : (Y.down p).1 ≫ genι Z = spMap (Var.evStalk p) ≫ stalkPt Y.Y (Var.base p) ≫ Y.π ≫ genι Z := by
    rw [← Category.assoc, Y.spMap_evStalk p]; rfl
  have hκ : (algebraMap (Y.Y.X.presheaf.stalk (Var.base p)) Y.Y.X.functionField).comp gm = fnOf U (gen_mem hy) :=
    RingHom.ext fun a => algebraMap_germ _ a
  have ha : frs.Tri (algebraMap _ Y.Y.X.functionField) Y.f0 t := by
    refine ⟨by rw [hT.1, hxs, ← hκ, ← spMap_comp_spMap gm, Category.assoc], by rw [hT.2.1, ← hκ]; rfl, fun τ i => ?_⟩
    have h3 := hT.2.2 τ i
    rw [← hκ] at h3
    simpa only [hfrs τ, GradedPieces.dual_comp] using h3
  have hφs : embOf e σ = (Var.evStalk p).comp (gm.comp φ) := by
    rw [hφg, ← hgm]; rfl
  exact (FlagCpt.adapted_of_tri (Y.spMap_evStalk p).symm ha (hgs.tri hφs hxp)).1

end Frames

section Main

open Limits GlobalTheory.ShFam.Pad

theorem exists_frames_chart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β) [SmoothOfRelativeDimension Dw.dim (genStr Z)] (F : Type) [Field F] [NumberField F] (e : F ≃+* c.F) (Y : FlagCpt Z e) (d : ℕ) (M : Man d) (I : ManIs M Y.Y) (a : Fin (M.n + 1)) (ψ : OpenPartialHomeomorph (M.X a) (Fin d → ℂ)), IsCompatChart (M.A a) ψ → 0 ∈ ψ.target → ∃ (ρ : ℝ) (t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Y.Y.Fnˣ) (g : ∀ z : Fin d → ℂ, Y.FrameAt (I.pt a (ψ.symm z))), 0 < ρ ∧ Metric.ball 0 ρ ⊆ ψ.target ∧ (∀ z ∈ Metric.ball (0 : Fin d → ℂ) ρ, Y.Adapted (I.pt a (ψ.symm z)) t (g z) 1) ∧ HolFam (Metric.ball 0 ρ) (fun z => (⟨Y.down (I.pt a (ψ.symm z)), g z⟩ : CxFr Z (embOf e (I.ε a)))) ∧ ContinuousOn (fun z => Y.down (I.pt a (ψ.symm z))) (Metric.ball 0 ρ) ∧ ∀ G : EigMet Z (embOf e (I.ε a)), G.SmoothOn (manifold Z (embOf e (I.ε a))) Set.univ → ∀ τ, GlobalTheory.HermFrame.IsPosFrame (Metric.ball 0 ρ) fun z => (G.gram (Y.down (I.pt a (ψ.symm z))) (g z) τ)ᵀ := by
  intro E _ _ _ H Dw l Xo c O _ β Z _ F _ _ e Y d M I a ψ hψ h0
  have hP := isHolTo_pt_symm I a ψ hψ
  have hPc : ContinuousOn (fun z => I.pt a (ψ.symm z)) ψ.target :=
    (I.pt a).continuous.comp_continuousOn ψ.continuousOn_symm
  obtain ⟨U, t, V, φV, Fr, hU, φU, fr, A, hyU, hφV, hUV, -, hfr⟩ :=
    exists_frames_nhds_spread E H Dw l Xo c O β Z F e Y (I.ε a) (Var.base (I.pt a (ψ.symm 0)))
  have hΩ : IsOpen (ψ.target ∩ (fun z => I.pt a (ψ.symm z)) ⁻¹' ptsIn Y.Y.str (I.ε a) U) :=
    hPc.isOpen_inter_preimage ψ.open_target (isOpen_ptsIn _)
  have h0U : I.pt a (ψ.symm 0) ∈ ptsIn Y.Y.str (I.ε a) U := CxPts.mem_ptsIn.2 hyU
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 hΩ 0 ⟨h0, h0U⟩
  have hbt : Metric.ball (0 : Fin d → ℂ) ρ ⊆ ψ.target := fun z hz => (hball hz).1
  have hbU : ∀ z ∈ Metric.ball (0 : Fin d → ℂ) ρ, I.pt a (ψ.symm z) ∈ ptsIn Y.Y.str (I.ε a) U :=
    fun z hz => (hball hz).2
  choose hv gsel fsel hgad hgfr hfFr hco using hfr
  classical
  let g : ∀ z : Fin d → ℂ, Y.FrameAt (I.pt a (ψ.symm z)) := fun z =>
    if h : I.pt a (ψ.symm z) ∈ ptsIn Y.Y.str (I.ε a) U then gsel _ h else (Y.exists_adapted _).choose.2
  have hg : ∀ z (h : I.pt a (ψ.symm z) ∈ ptsIn Y.Y.str (I.ε a) U), g z = gsel _ h := fun z h => dif_pos h
  let ev' : (Fin d → ℂ) → (Γ(Y.Y.X, U) →+* ℂ) := fun z =>
    if h : I.pt a (ψ.symm z) ∈ ptsIn Y.Y.str (I.ε a) U then evHom h else evHom h0U
  have hev' : ∀ z (h : I.pt a (ψ.symm z) ∈ ptsIn Y.Y.str (I.ε a) U), ev' z = evHom h := fun z h => dif_pos h
  have hPΩ := LocLift.isHolTo_mono hP hΩ Set.inter_subset_left
  have hdev : ∀ r : Γ(Y.Y.X, U), DifferentiableOn ℂ (fun z => ev' z r) (Metric.ball 0 ρ) := fun r z hz =>
    (HolLieFrame.differentiableAt_ev hPΩ (show Sp Γ(Y.Y.X, U) ⟶ Y.Y.X from hU.fromSpec) ev'
      (fun b hb => by rw [hev' b hb.2]; exact (Points.specMap_valMap_fromSpec hU _ hb.2).symm)
      (hball hz) r).differentiableWithinAt
  refine ⟨ρ, t, g, hρ, hbt, fun z hz => ?_, ⟨?_, fun τ i => ?_⟩, ?_, fun G hG τ => ?_⟩
  · rw [hg z (hbU z hz)]; exact hgad _ _
  · exact LocLift.isHolTo_comp_hom (LocLift.isHolTo_mono hP Metric.isOpen_ball hbt) Y.π
  · refine HolFrames.holTan_dualMap Metric.isOpen_ball (fr.v τ i) (fun z hz => evHom (hbU z hz))
      (fun r => ⟨fun z => ev' z r, hdev r, fun z hz => by show _ = ev' z r; rw [hev' z (hbU z hz)]⟩) (fun z hz => ?_)
    show (g z).v τ i = _
    rw [hg z (hbU z hz)]
    exact hgfr _ _ τ i
  · exact (CxPts.continuous_of_comp (m := Y.down (σ := I.ε a)) (f := Y.π) (fun _ => rfl)).comp_continuousOn (hPc.mono hbt)
  · choose gf hre him hgf using fun (k k' : Fin (Dw.mult τ)) => hG V φV Fr τ k k' hφV
    let Mf : Y.Y.pts (I.ε a) → Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ :=
      fun q => Matrix.of fun k k' => gf k k' (Y.down q)
    let Af : Y.Y.pts (I.ε a) → Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ :=
      fun q => Matrix.of fun k k' => ev Y.Y.str (I.ε a) U (A τ k k') q
    have hM : ∀ k k', (Y.Y.an (I.ε a)).SmoothOn (ptsIn Y.Y.str (I.ε a) U) (fun q => (Mf q k k').re) ∧
        (Y.Y.an (I.ε a)).SmoothOn (ptsIn Y.Y.str (I.ε a) U) (fun q => (Mf q k k').im) := fun k k' =>
      ⟨((hre k k').comp_map (isOpen_univ.inter (isOpen_ptsIn _)) (m := Y.down) (f := Y.π) (fun _ => rfl)
          (Y.Y.an (I.ε a))).mono fun q hq => ⟨trivial, hUV q hq⟩,
        ((him k k').comp_map (isOpen_univ.inter (isOpen_ptsIn _)) (m := Y.down) (f := Y.π) (fun _ => rfl)
          (Y.Y.an (I.ε a))).mono fun q hq => ⟨trivial, hUV q hq⟩⟩
    have hA : ∀ k k', (Y.Y.an (I.ε a)).HoloOn (ptsIn Y.Y.str (I.ε a) U) (fun q => Af q k k') :=
      fun k k' => AnRead.holoOn_ev_of_subset _ (fun _ hq => hq)
    have hsm := AnRead.smoothOn_conjTranspose_mul_mul (Y.Y.an (I.ε a)) _ (isOpen_ptsIn _) Af Mf hA hM
    have hgram : ∀ z ∈ Metric.ball (0 : Fin d → ℂ) ρ, G.gram (Y.down (I.pt a (ψ.symm z))) (g z) τ =
        (Af (I.pt a (ψ.symm z)))ᴴ * Mf (I.pt a (ψ.symm z)) * Af (I.pt a (ψ.symm z)) := by
      intro z hz
      have hq := hbU z hz
      have e1 : (fsel _ hq).co (gsel _ hq) τ = Af (I.pt a (ψ.symm z)) := by
        rw [hco _ hq τ]; ext k k'; simp [Af, ev_eq hq]
      have e2 : G.gram (Y.down (I.pt a (ψ.symm z))) (fsel _ hq) τ = Mf (I.pt a (ψ.symm z)) := by
        ext k k'; exact hgf k k' _ trivial (hv _ hq) (fsel _ hq) (hfFr _ hq)
      rw [hg z hq, G.change _ (fsel _ hq) (gsel _ hq) τ, e1, e2]
    refine ⟨Metric.isOpen_ball, fun k k' => ?_, fun z hz => (G.pos _ _ τ).transpose⟩
    have h1 := (contDiffOn_comp_pt_symm I a ψ hψ (Y.Y.an (I.ε a)) (isOpen_ptsIn _) (hsm k' k).1).mono hball
    have h2 := (contDiffOn_comp_pt_symm I a ψ hψ (Y.Y.an (I.ε a)) (isOpen_ptsIn _) (hsm k' k).2).mono hball
    have h3 := (Complex.ofRealCLM.contDiff.comp_contDiffOn h1).add
      ((Complex.ofRealCLM.contDiff.comp_contDiffOn h2).mul (contDiffOn_const (c := Complex.I)))
    refine h3.congr fun z hz => ?_
    rw [Matrix.transpose_apply, hgram z hz]
    simp only [Function.comp_apply, Complex.ofRealCLM_apply]
    exact (Complex.re_add_im _).symm

end Main

end GlobalTheory.ShFam.CurvFrames
