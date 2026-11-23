import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsHodgeFrameIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniformizedFamilyChartIndex
open AlgebraicGeometry CategoryTheory Limits NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.GradedNorm GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open GlobalTheory.ArcQ
open scoped ContDiff

set_option autoImplicit false

namespace GlobalTheory.ShFam

section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem oF_pt_ext {Z : Model Xo c (algebraMap (𝓞 c.F) c.F)} {R : Type} [CommRing R] {w w' : Sp R ⟶ Z.oF.t.G.left}
    (h0 : w ≫ Z.m0.toSABMap.φ = w' ≫ Z.m0.toSABMap.φ) (h : w ≫ Z.m.φ ≫ Z.t.G.hom = w' ≫ Z.m.φ ≫ Z.t.G.hom) : w = w' := by
  refine Z.m0.toSABMap.cart.1.hom_ext h0 ?_
  apply pullback.hom_ext
  · simp only [Category.assoc, ← Z.m0.toSABMap.cart.1.w]
    rw [reassoc_of% h0]
  · rw [← Z.jQ_over]
    obtain ⟨g, hg⟩ := Spec.map_surjective (w ≫ Z.oF.t.G.hom ≫ Z.jQ ≫ pullback.snd Z.s (spMap (algebraMap (𝓞 c.F) c.F)))
    obtain ⟨g', hg'⟩ := Spec.map_surjective (w' ≫ Z.oF.t.G.hom ≫ Z.jQ ≫ pullback.snd Z.s (spMap (algebraMap (𝓞 c.F) c.F)))
    have e1 : ∀ v : Sp R ⟶ Z.oF.t.G.left, (v ≫ Z.oF.t.G.hom ≫ Z.jQ ≫ pullback.snd _ _) ≫
        spMap (algebraMap (𝓞 c.F) c.F) = (v ≫ Z.m.φ ≫ Z.t.G.hom) ≫ Z.s := fun v => by
      simp only [Category.assoc, ← pullback.condition]
      rw [← reassoc_of% Z.m.cart.1.w]
    have hh : Spec.map g ≫ spMap (algebraMap (𝓞 c.F) c.F) = Spec.map g' ≫ spMap (algebraMap (𝓞 c.F) c.F) := by
      rw [hg, hg', e1, e1, h]
    rw [← Spec.map_comp, ← Spec.map_comp] at hh
    have h2 := congrArg CommRingCat.Hom.hom (Spec.map_injective hh)
    have h3 : g.hom = g'.hom := IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 c.F)) (by simpa using h2)
    simp only [Category.assoc]
    rw [← hg, ← hg', CommRingCat.hom_ext h3]

end
end GlobalTheory.ShFam

namespace GlobalTheory.ShFam.ToroidalCompactificationData

theorem hodge_gram_of_sameVec : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (x : ToroidalCompactificationData s) (σ : κ.c.F →+* ℂ), Formalism.L2.PjFree.GoodEmb κ.c σ → ∀ (W : UnfWit (s.U σ)) (i : Fin W.F.n) (P : (W.F.Di i).La →+ (Fin W.g → ℂ)), IsPeriod (W.F.Di i) (fun j => Formalism.L2.PjFree.relab κ.c σ (W.e j).1) P → ∀ (Hm : Matrix (Fin W.g) (Fin W.g) ℂ), IsRiem W.F i P Hm → ∀ (q : FrPt (S.Xo κ.l) κ.c (CAt σ)) (z : ∀ τ : D.host.E →+* ℂ, Fin (S.Dw.mult τ) → (Fin W.g → ℂ)), AnLie W.F i P q z → ∀ (y : CxPts (genStr s.T.Z) σ), cxPt s.T.Z q = y → ∀ f : EigFrame s.T.Z σ (y.1 ≫ genι s.T.Z), (∀ τ k, ∃ w : Sp (DualNumber ℂ) ⟶ s.T.Z.oF.t.G.left, w ≫ s.T.Z.m0.toSABMap.φ = q.u τ k ∧ w ≫ s.T.Z.m.φ = f.v τ k) → ∀ τ a b, (x.hodge σ).gram y f τ a b = (Real.pi : ℂ) * hermForm Hm (z τ b) (z τ a) := by
  intro D A N j S κ s x σ hσ W i P hP Hm hH q z hq y hy f hf τ a b
  subst hy
  have hv : ∀ τ k, f.v τ k = (cxFrame s.T.Z q).v τ k := by
    intro τ k
    obtain ⟨w, hw0, hw⟩ := hf τ k
    obtain ⟨w', -, hw0', hw'⟩ := EigFrame.ofFrPt_v (S := CAt σ) s.T.Z q (Category.assoc _ _ _).symm τ k
    have hb : w ≫ s.T.Z.m.φ ≫ s.T.Z.t.G.hom = w' ≫ s.T.Z.m.φ ≫ s.T.Z.t.G.hom := by
      rw [reassoc_of% hw, reassoc_of% hw', (f.tan τ k).1]
      exact ((cxFrame s.T.Z q).tan τ k).1.symm
    have e : w = w' := oF_pt_ext (hw0.trans hw0'.symm) hb
    rw [← hw, e]
    exact hw'
  have hco : (cxFrame s.T.Z q).co f τ = 1 := by
    refine EigFrame.co_eq fun k => ?_
    rw [hv τ k]
    convert isCombAtG_single _ _ ((cxFrame s.T.Z q).tan τ) k using 1
    funext a
    simp [Matrix.one_apply, Pi.single_apply]
  rw [(x.hodge σ).change _ (cxFrame s.T.Z q) f τ, hco, x.hodge_gram_riemann hσ W hP hH hq τ]
  simp

end GlobalTheory.ShFam.ToroidalCompactificationData
