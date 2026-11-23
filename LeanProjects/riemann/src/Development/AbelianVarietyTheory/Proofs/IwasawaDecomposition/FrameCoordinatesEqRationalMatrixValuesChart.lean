import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LieGramEqGramOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineStableLieEigenspaceFrame
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.AntisymmFibrePointTwo
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsConjFsBasisOfUnitary
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LinearIndependentOfCutSec
open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.LieBase GlobalTheory.CxPts GlobalTheory.Cartier
open Filter Topology
open scoped Matrix

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LieBase.ChartCoords

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}

theorem co_congr {R : Type} [CommRing R] {φ : c.F →+* R} {x : Sp R ⟶ Z.X} {f f' g : EigFrame Z φ x}
    (h : ∀ τ i, f'.v τ i = f.v τ i) (τ : E →+* ℂ) : f'.co g τ = f.co g τ :=
  EigFrame.co_eq fun i => by rw [funext (h τ)]; exact f.co_spec g τ i

theorem v_of_isMap_trans {R R₁ R₂ : Type} [CommRing R] [CommRing R₁] [CommRing R₂] {φ : c.F →+* R}
    {x : Sp R ⟶ Z.X} {φ₁ : c.F →+* R₁} {x₁ : Sp R₁ ⟶ Z.X} {φ₂ : c.F →+* R₂} {x₂ : Sp R₂ ⟶ Z.X}
    {f : EigFrame Z φ x} {f₁ : EigFrame Z φ₁ x₁} {f₂ f₂' : EigFrame Z φ₂ x₂} {ψ₁ : R →+* R₁} {ψ₂ : R₁ →+* R₂}
    {ψ : R →+* R₂} (h₁ : f.IsMap ψ₁ f₁) (h₂ : f₁.IsMap ψ₂ f₂) (h : f.IsMap ψ f₂') (hψ : ψ₂.comp ψ₁ = ψ)
    (τ : E →+* ℂ) (i : Fin (Dw.mult τ)) : f₂.v τ i = f₂'.v τ i := by
  rw [h₂ τ i, h₁ τ i, GlobalTheory.GradedPieces.dual_comp, hψ, h τ i]

end GlobalTheory.LieBase.ChartCoords

open GlobalTheory.ProjVar.Var GlobalTheory.LieBase.ChartCoords

theorem GlobalTheory.LieBase.coords_eq_ratVal_of_chart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (F : Type) [Field F] (e : F ≃+* c.F) (X : Var F) (j : X.X ⟶ gen Z) (f₀ : EigFrame Z (constF e X) (genericPt X ≫ j ≫ genι Z)) (S : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr Z ≫ spMap e.toRingHom = X.str), IsOpenImmersion j → Tied e X j f₀ S A₀ → ∀ (V : (gen Z).affineOpens) (φ : c.F →+* Γ(gen Z, V.1)) (Φ : EigFrame Z φ (LogKS.chart V ≫ genι Z)), LogKS.chart V ≫ genStr Z = spMap φ → ∀ A : Mat Dw.mult X.Fn, ∃ M : Mat Dw.mult X.Fn, ∀ z : GlobalTheory.CxPts X.str (σ.comp e.toRingHom), A ∈ S.S (under z) → ∀ hz : cxOf e σ hj z ∈ ptsIn (genStr Z) σ V.1, (∀ τ p q, RegAt (under z) (M τ p q)) ∧ (∃ g : EigFrame Z σ ((cxOf e σ hj z).1 ≫ genι Z), FrameAt e f₀ A₀ A z g) ∧ ∀ g : EigFrame Z σ ((cxOf e σ hj z).1 ≫ genι Z), FrameAt e f₀ A₀ A z g → ∀ f : EigFrame Z σ ((cxOf e σ hj z).1 ≫ genι Z), Φ.IsMap (evHom hz) f → ∀ τ, f.co g τ = (M τ).map (fun r => ratVal r z) := by
  intro E _ _ _ H Dw l Xo c O _ β Z σ F _ e X j f₀ S A₀ hj _hoi hT V φ Φ hV A
  classical
  have hVa : IsAffineOpen V.1 := V.2
  haveI : Mono (LogKS.chart V) := inferInstanceAs (Mono hVa.fromSpec)
  have hmem : ∀ z : GlobalTheory.CxPts X.str (σ.comp e.toRingHom), cxOf e σ hj z ∈ ptsIn (genStr Z) σ V.1 →
      under z ∈ j ⁻¹ᵁ V.1 := fun z hz => mem_ptsIn.1 hz
  by_cases hη : genericPoint X.X ∈ j ⁻¹ᵁ V.1
  swap
  · exact ⟨0, fun z _ hz => absurd (gen_mem (hmem z hz)) hη⟩
  have key : ∀ x : X.X, x ∈ j ⁻¹ᵁ V.1 → ∃ ψ : Γ(gen Z, V.1) →+* X.X.presheaf.stalk x,
      spMap ψ ≫ LogKS.chart V = stalkPt X x ≫ j := fun x hx =>
    TieBase.exists_affine_factor _ V.2 (by
      show j (X.X.fromSpecStalk x (IsLocalRing.closedPoint _)) ∈ V.1
      rw [Scheme.fromSpecStalk_closedPoint]; exact hx)
  have key' : ∀ (x : X.X) (ψ : Γ(gen Z, V.1) →+* X.X.presheaf.stalk x), spMap ψ ≫ LogKS.chart V = stalkPt X x ≫ j →
      spMap ((algebraMap (X.X.presheaf.stalk x) X.X.functionField).comp ψ) ≫ LogKS.chart V = genericPt X ≫ j :=
    fun x ψ h => by rw [TieBase.spMap_trans, Category.assoc, h, TieBase.genericPt_eq X x, Category.assoc]
  obtain ⟨ψη, hψη⟩ := key _ hη
  obtain ⟨ρ, h₀⟩ : ∃ ρ : Γ(gen Z, V.1) →+* X.X.functionField, spMap ρ ≫ LogKS.chart V = genericPt X ≫ j :=
    ⟨_, key' _ ψη hψη⟩
  have hφK : constF e X = ρ.comp φ := EigLoc.spMap_inj (by
    rw [← TieBase.genericPt_str e X j hj, ← h₀, Category.assoc, hV, ← TieBase.spMap_trans])
  obtain ⟨ΦK, hΦK⟩ := Φ.exists_isMap ρ hφK (x' := genericPt X ≫ j ≫ genι Z)
    (by rw [← Category.assoc, ← h₀, Category.assoc])
  refine ⟨fun τ => ΦK.co f₀ τ * (((A₀ * A⁻¹) τ)ᵀ)⁻¹, fun z hA hz => ?_⟩
  have hx := hmem z hz
  obtain ⟨φx, fz, hc⟩ := hT.2 (under z) A hA
  obtain ⟨ψx, hψx⟩ := key _ hx
  have hρx : (algebraMap _ X.X.functionField).comp ψx = ρ :=
    EigLoc.spMap_inj ((cancel_mono (LogKS.chart V)).1 ((key' _ ψx hψx).trans h₀.symm))
  have hφx : φx = ψx.comp φ := RingHom.ext fun a => IsFractionRing.injective (X.X.presheaf.stalk (under z))
    X.X.functionField (by
      have h1 := RingHom.congr_fun hc.2.1 a
      have h2 := RingHom.congr_fun hφK a
      rw [← hρx] at h2
      exact h1.symm.trans h2)
  obtain ⟨Φx, hΦx⟩ := Φ.exists_isMap ψx hφx (x' := stalkPt X (under z) ≫ j ≫ genι Z)
    (by rw [← Category.assoc, ← hψx, Category.assoc])
  have hM : ∀ fz' : EigFrame Z φx (stalkPt X (under z) ≫ j ≫ genι Z),
      fz'.Coord (algebraMap (X.X.presheaf.stalk (under z)) X.X.functionField) f₀ (A₀ * A⁻¹) → ∀ τ,
      ΦK.co f₀ τ * (((A₀ * A⁻¹) τ)ᵀ)⁻¹ = (Φx.co fz' τ).map (algebraMap _ X.X.functionField) := by
    intro fz' hc' τ
    obtain ⟨k, hk⟩ := fz'.exists_isMap _ hc'.2.1 hc'.1
    obtain ⟨Φk, hΦk⟩ := Φx.exists_isMap _ hc'.2.1 hc'.1
    have h1 : k.co f₀ τ = ((A₀ * A⁻¹) τ)ᵀ := EigFrame.co_eq fun i => by rw [funext (hk τ)]; exact hc'.2.2 τ i
    have h3 : Φk.co k τ = (Φx.co fz' τ).map (algebraMap _ X.X.functionField) := hΦk.co τ hk hc'.1
    have h4 : Φk.co f₀ τ = ΦK.co f₀ τ := co_congr (v_of_isMap_trans hΦx hΦk hΦK hρx) τ
    have h5 : f₀.co k τ = (k.co f₀ τ)⁻¹ := (Matrix.inv_eq_right_inv ((k.co_mul f₀ k τ).trans (k.co_self τ))).symm
    rw [← h3, ← Φk.co_mul f₀ k τ, h4, h5, h1]
  have hs : spMap (Scheme.stalkClosedPointTo z.1).hom ≫ stalkPt X (under z) = z.1 :=
    Scheme.Spec_stalkClosedPointTo_fromSpecStalk z.1
  have hxz : (cxOf e σ hj z).1 ≫ genι Z = spMap (Scheme.stalkClosedPointTo z.1).hom ≫ stalkPt X (under z) ≫ j ≫ genι Z := by
    show (z.1 ≫ j) ≫ genι Z = _
    conv_lhs => rw [← hs]
    simp only [Category.assoc]
  refine ⟨fun τ p q => ?_, ?_, ?_⟩
  · beta_reduce
    rw [hM fz hc τ]
    exact ⟨Φx.co fz τ p q, rfl⟩
  · have hφ : σ = (Scheme.stalkClosedPointTo z.1).hom.comp φx := RingHom.ext fun a => by
      have h3 : φx a = algebraMap F _ (e.symm a) := IsFractionRing.injective _ X.X.functionField
        ((RingHom.congr_fun hc.2.1 a).symm.trans ((X.stalkIncl (under z)).commutes _).symm)
      show σ a = evStalk z (φx a)
      rw [h3]
      refine Eq.trans ?_ ((evStalk_germ (U := ⊤) trivial _).trans (ev_algX mem_ptsIn_top _)).symm
      simp
    obtain ⟨g, hg⟩ := fz.exists_isMap _ hφ hxz
    exact ⟨g, φx, fz, _, (Scheme.Spec_stalkClosedPointTo_fromSpecStalk z.1).symm, hc, hg⟩
  · rintro g ⟨φ', fz', ψ', hψ', hc', hm'⟩ f hf τ
    obtain rfl : ψ' = (Scheme.stalkClosedPointTo z.1).hom :=
      EigLoc.spMap_inj ((cancel_mono (X.X.fromSpecStalk (under z))).1
        (hψ'.symm.trans (Scheme.Spec_stalkClosedPointTo_fromSpecStalk z.1).symm))
    obtain rfl : φ' = φx := RingHom.ext fun a => IsFractionRing.injective _ X.X.functionField
      ((RingHom.congr_fun hc'.2.1 a).symm.trans (RingHom.congr_fun hc.2.1 a))
    have hev : (Scheme.stalkClosedPointTo z.1).hom.comp ψx = evHom hz :=
      EigLoc.spMap_inj ((cancel_mono (LogKS.chart V)).1 (by
        rw [TieBase.spMap_trans, Category.assoc, hψx, LieMet.spMap_evHom hz, ← Category.assoc, hs]
        rfl))
    have hfx : Φx.IsMap (Scheme.stalkClosedPointTo z.1).hom f := fun τ i => by
      rw [hf τ i, hΦx τ i, GlobalTheory.GradedPieces.dual_comp, hev]
    beta_reduce
    rw [hfx.co τ hm' hxz, hM fz' hc' τ]
    refine Matrix.ext fun a b => ?_
    simp only [Matrix.map_apply]
    rw [GlobalTheory.TrueGeo.Res.ratVal_eq_valAt z ⟨_, rfl⟩, GlobalTheory.TrueGeo.Res.valAt_algebraMap]
