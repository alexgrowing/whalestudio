import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsHodgeFrameIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniformizedFamilyChartIndex
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GramSmoothOfHolomorphicFrames
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsExponentialModelFiberOfUniformisationExp
open AlgebraicGeometry CategoryTheory Limits NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.GradedNorm GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open GlobalTheory.ArcQ
open scoped ContDiff

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.ModelExpCoord

open GlobalTheory.ShFam.Hor.LogCh
open ReciprocityTheory.ChartRestriction.G.PullbackSections.ExpRows (isDerivAt0_unique)

theorem coord_holomorphic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (i : Fin Fu.n) (n : ℕ) (B : Set (Fin n → ℂ)) (P : (Fin n → ℂ) → ((Fu.Di i).La →+ (Fin g → ℂ))) (p : (Fin n → ℂ) → (Sp ℂ ⟶ Xo.XF c)) (hu : ∀ b, Fu.u i (P b) = p b ≫ pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)) (V : (gen Z).affineOpens) (v : Sp (DualNumber Γ(gen Z, V.1)) ⟶ Z.t.G.left), IsOpen B → (∀ b, IsPeriod (Fu.Di i) ty (P b)) → (∀ a, DifferentiableOn ℂ (fun b => P b a) B) → (∀ b, p b ≫ pullback.snd _ _ = spMap σ) → IsTanAtG Z.t (LogKS.chart V ≫ genι Z) v → ∃ W : (Fin n → ℂ) → (Fin g → ℂ), DifferentiableOn ℂ W {b ∈ B | ⊤ ≤ (p b ≫ Z.jQ) ⁻¹ᵁ V.1} ∧ ∀ b ∈ B, ∀ (y : CxPts (genStr Z) σ) (hy : y ∈ ptsIn (genStr Z) σ V.1), y.1 = p b ≫ Z.jQ → IsDerivAt0 (fun z => GlobalTheory.ShFam.Hor.LogCh.liftEx Z Fu (p b) i (P b) (hu b) z ≫ Z.m.φ) (W b) (spMap (Formalism.L2.Pj.dualMap (evHom hy)) ≫ v) := by
  intro E _ _ _ H Dw l Xo c O _ β Z σ g ty Fu i n B P p hu V v hB hP hPd hs hv
  classical
  have h1 := Fu.hol i n B P hB ⟨fun b _ => hP b, hPd⟩
  have hp : IsHolTo B p := TrueCx.TorHolo.isHolTo_of_fst _ _ hB (spMap σ) hs
    (LocLift.isHolTo_congr h1.1 fun b _ => (hu b).symm)
  have h2 := TrueCx.TorFrHolo.isHolTo_lift Z.m0.toSABMap.cart.1 hB (fun b z => (Fu.ex i (P b) z).left) p h1.2 hp
    (fun b z => by rw [Over.w (Fu.ex i (P b) z), ← hu b]; rfl)
  have hFt : IsHolTo (B ×ˢ Set.univ) (fun bz : (Fin n → ℂ) × (Fin g → ℂ) =>
      liftEx Z Fu (p bz.1) i (P bz.1) (hu bz.1) bz.2 ≫ Z.m.φ) :=
    ReciprocityTheory.ChartRestriction.G.PullbackSections.isHolTo_comp h2 Z.m.φ
  have hY : IsHolTo B fun b => p b ≫ Z.jQ := ReciprocityTheory.ChartRestriction.G.PullbackSections.isHolTo_comp hp Z.jQ
  set B' := {b ∈ B | ⊤ ≤ (p b ≫ Z.jQ) ⁻¹ᵁ V.1} with hB'def
  have hB' : IsOpen B' := (hY V.1 0).1
  let yb : (Fin n → ℂ) → CxPts (genStr Z) σ := fun b =>
    ⟨p b ≫ Z.jQ, by rw [Category.assoc, Z.jQ_over]; exact hs b⟩
  have hm : ∀ b, ⊤ ≤ (p b ≫ Z.jQ) ⁻¹ᵁ V.1 → yb b ∈ ptsIn (genStr Z) σ V.1 := fun b h => h
  have hExp : ∀ b, IsExpAt Z.t (p b ≫ Z.jQ ≫ genι Z)
      (pushEx Z Fu (p b) i (P b) (p b ≫ Z.jQ ≫ genι Z) (hu b) rfl) := fun b =>
    isExpAt_pushEx E H Dw l Xo c O β Z g ty _ Fu (p b) i (P b) (p b ≫ Z.jQ ≫ genι Z) (hu b) rfl (hP b)
  have hTan : ∀ b (h : ⊤ ≤ (p b ≫ Z.jQ) ⁻¹ᵁ V.1),
      IsTanAtG Z.t (p b ≫ Z.jQ ≫ genι Z) (spMap (Formalism.L2.Pj.dualMap (evHom (hm b h))) ≫ v) := fun b h =>
    isTan_map (evHom (hm b h)) (by rw [← Category.assoc, spMap_evHom]; rfl) hv
  have hW0 : ∀ b (h : ⊤ ≤ (p b ≫ Z.jQ) ⁻¹ᵁ V.1), ∃! w, IsDerivAt0
      (fun z => liftEx Z Fu (p b) i (P b) (hu b) z ≫ Z.m.φ) w
      (spMap (Formalism.L2.Pj.dualMap (evHom (hm b h))) ≫ v) := fun b h =>
    (hExp b).2.2 _ (hTan b h)
  let W : (Fin n → ℂ) → Fin g → ℂ := fun b =>
    if h : ⊤ ≤ (p b ≫ Z.jQ) ⁻¹ᵁ V.1 then (hW0 b h).exists.choose else 0
  have hWd : ∀ b (h : ⊤ ≤ (p b ≫ Z.jQ) ⁻¹ᵁ V.1), IsDerivAt0
      (fun z => liftEx Z Fu (p b) i (P b) (hu b) z ≫ Z.m.φ) (W b)
      (spMap (Formalism.L2.Pj.dualMap (evHom (hm b h))) ≫ v) := fun b h => by
    have e : W b = (hW0 b h).exists.choose := dif_pos h
    rw [e]
    exact (hW0 b h).exists.choose_spec
  have : IsOpenImmersion (LogKS.chart V) := IsAffineOpen.isOpenImmersion_fromSpec V.2
  have hdiff : ∀ b₀ ∈ B', DifferentiableAt ℂ W b₀ := fun b₀ hb₀ => by
    have h₀ : ⊤ ≤ (p b₀ ≫ Z.jQ) ⁻¹ᵁ V.1 := hb₀.2
    let ev : (Fin n → ℂ) → (Γ(gen Z, V.1) →+* ℂ) := fun b =>
      if h : ⊤ ≤ (p b ≫ Z.jQ) ⁻¹ᵁ V.1 then evHom (hm b h) else evHom (hm b₀ h₀)
    have hevb : ∀ b (h : ⊤ ≤ (p b ≫ Z.jQ) ⁻¹ᵁ V.1), ev b = evHom (hm b h) := fun b h => dif_pos h
    have hev : ∀ cc, DifferentiableAt ℂ (fun b => ev b cc) b₀ :=
      HolLieFrame.differentiableAt_ev (B := B') (LocLift.isHolTo_mono hY hB' fun b hb => hb.1) (LogKS.chart V) ev
        (fun b hb => by rw [hevb b hb.2]; exact (spMap_evHom (hm b hb.2)).symm) hb₀
    have hder : ∀ b ∈ B', IsDerivAt0 (fun z => liftEx Z Fu (p b) i (P b) (hu b) z ≫ Z.m.φ) (W b)
        (spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR (ev b)) ≫ v) := fun b hb => by
      rw [hevb b hb.2]
      exact hWd b hb.2
    refine HolLieFrame.differentiableAt_of_forms W b₀ fun w hw => ?_
    have hw' : ∀ (O : Z.t.G.left.Opens) (f : Γ(Z.t.G.left, O)),
        ⊤ ≤ (liftEx Z Fu (p b₀) i (P b₀) (hu b₀) 0 ≫ Z.m.φ) ⁻¹ᵁ O →
        fderiv ℂ (fun z => valAt' (liftEx Z Fu (p b₀) i (P b₀) (hu b₀) z ≫ Z.m.φ) O f) 0 w = 0 := by
      intro O f hO
      refine hw (fun b => fderiv ℂ (fun z => valAt' (liftEx Z Fu (p b) i (P b) (hu b) z ≫ Z.m.φ) O f) 0)
        (HolLieFrame.differentiableAt_fderiv
          (e := fun b z => liftEx Z Fu (p b) i (P b) (hu b) z ≫ Z.m.φ) hFt hb₀.1 O f hO) ?_
      obtain ⟨Fn, hF, hF'⟩ := HolLieFrame.exists_hol_snd v ev b₀ hev O f
        ((TangentOrigin.top_le_preimage_iff _ O).2 (by rw [(hder b₀ hb₀).1]; exact hO))
      refine hF.congr_of_eventuallyEq ?_
      filter_upwards [hF', hB'.mem_nhds hb₀] with b ⟨h, e'⟩ hb
      exact ((hder b hb).2 O h f).symm.trans e'
    have d₁ := LocalLift.isDerivAt0_const (fun z => liftEx Z Fu (p b₀) i (P b₀) (hu b₀) z ≫ Z.m.φ) w hw'
    have d₀ := LocalLift.isDerivAt0_const (fun z => liftEx Z Fu (p b₀) i (P b₀) (hu b₀) z ≫ Z.m.φ) 0
      fun _ _ _ => map_zero _
    obtain ⟨u, ⟨hut, hud⟩, -⟩ := (hExp b₀).2.1 0
    have hu0 := isDerivAt0_unique hud d₀
    obtain ⟨w', -, hw''⟩ := (hExp b₀).2.2 u hut
    have a1 : w = w' := hw'' w (by rw [hu0]; exact d₁)
    have a0 : (0 : Fin g → ℂ) = w' := hw'' 0 hud
    exact a1.trans a0.symm
  refine ⟨W, fun b hb => (hdiff b hb).differentiableWithinAt, fun b _ y hy hyb => ?_⟩
  have hyb' : y = yb b := Subtype.ext hyb
  subst hyb'
  exact hWd b hy

end GlobalTheory.ModelExpCoord
