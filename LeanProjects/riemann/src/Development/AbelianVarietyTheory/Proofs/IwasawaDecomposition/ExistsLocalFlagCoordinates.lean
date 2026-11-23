import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DualGramInterpGram
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineEigenframeFlag
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalEquationComplexPoints
open AlgebraicGeometry CategoryTheory Limits NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open scoped ComplexOrder

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ShFam.FlagFrames

attribute [local instance] Over.cartesianMonoidalCategory

theorem exists_frames_nhds : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β) (F : Type) [Field F] [NumberField F] (e : F ≃+* c.F) (Y : FlagCpt Z e) (σ : F →+* ℂ) (y : Y.Y.X), ∃ (U : Y.Y.X.Opens) (t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Y.Y.Fnˣ) (V : (gen Z).affineOpens) (φ : c.F →+* Γ(gen Z, V.1)) (Fr : EigFrame Z φ (LogKS.chart V ≫ genι Z)) (A : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) Γ(Y.Y.X, U)), y ∈ U ∧ LogKS.chart V ≫ genStr Z = spMap φ ∧ (∀ p : Y.Y.pts σ, p ∈ ptsIn Y.Y.str σ U → Y.down p ∈ ptsIn (genStr Z) (embOf e σ) V.1) ∧ (∀ y' ∈ U, ∀ τ i, (Y.gr τ i).IsEqn y' (t τ i)) ∧ ∀ (p : Y.Y.pts σ) (hp : p ∈ ptsIn Y.Y.str σ U), ∃ (hv : Y.down p ∈ ptsIn (genStr Z) (embOf e σ) V.1) (g f : Y.FrameAt p), Y.Adapted p t g 1 ∧ Fr.IsMap (evHom hv) f ∧ ∀ τ, f.co g τ = (A τ).map (evHom hp) := by
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
  refine ⟨U, t, ⟨V₀, hV₀⟩, φ₀, Fr₀, fun τ => Fr'.co fr τ, hy, hs₀, hdown, ht, fun p hp => ⟨hdown p hp, ?_⟩⟩
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
  refine ⟨g, f, ?_, hf, fun τ => EigFrame.IsMap.co τ hf' hg hxg⟩
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

end GlobalTheory.ShFam.FlagFrames
