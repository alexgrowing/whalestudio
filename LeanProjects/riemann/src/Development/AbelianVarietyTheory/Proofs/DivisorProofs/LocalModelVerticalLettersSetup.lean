import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopLeOfClosedPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransitionCoefficientsPullbackStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UltrametricCoefficientBoundStatement
open CategoryTheory Limits AlgebraicGeometry IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.LocM GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains GlobalTheory.BundleChernComparison GlobalTheory.ChainPts
open GlobalTheory.Twist (resM)
open Formalism.MainNotions.DIV.Cons (intO)

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.ChainPts.PullHT

open GlobalTheory.VB (IsFrame IsVB)

theorem coef_pullS {X X' : Scheme.{0}} (g : X' ⟶ X) {F : X.Modules} [F.IsQuasicoherent] {r : ℕ} (d : Bool)
    {V V' : X.Opens} {U U' : X'.Opens} (hU : U ≤ g ⁻¹ᵁ V) (hU' : U' ≤ g ⁻¹ᵁ V')
    {e : Fin r → Γ(F, V)} {s : Fin r → Γ(F, V')} (he : IsFrame e) (hs : IsFrame s) (l i : Fin r) :
    coef d (isFrame_pullS g hU he) (isFrame_pullS g hU' hs) l i =
      (g.appLE (V ⊓ V') (U ⊓ U') (inf_le_inf hU hU')).hom (coef d he hs l i) :=
  GlobalTheory.T.transition_coefficients_pullback g d hU hU' he hs l i

theorem norm_coef_iff {X : Scheme.{0}} {F : X.Modules} {r : ℕ} (d : Bool) {V V₁ V' : X.Opens} {e : Fin r → Γ(F, V)}
    {e₁ : Fin r → Γ(F, V₁)} {s : Fin r → Γ(F, V')} (he : IsFrame e) (he₁ : IsFrame e₁) (hs : IsFrame s)
    (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] (w : Sp ↥(intO C) ⟶ X) (hV : ⊤ ≤ w ⁻¹ᵁ V)
    (hV₁ : ⊤ ≤ w ⁻¹ᵁ V₁) (cf : Fin r → C) :
    (∀ l, ‖∑ i, cf i * valF (spMap (intO C).subtype ≫ w) _ (coef d he hs l i)‖ ≤ 1) ↔
      ∀ l, ‖∑ i, cf i * valF (spMap (intO C).subtype ≫ w) _ (coef d he₁ hs l i)‖ ≤ 1 :=
  GlobalTheory.T.ultrametric_coefficient_bound d he he₁ hs C w hV hV₁ cf

end GlobalTheory.ChainPts.PullHT

namespace GlobalTheory.ChainPts.PullHT

open GlobalTheory.VB (IsFrame IsVB)

section Lat

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

theorem isLat_pull {Z : LocM.Mdl Y i₀} {X X' : Scheme.{0}} (g : X' ⟶ X) (h : X ⟶ Z.X) {r : ℕ}
    {x : Fin r → Letter Dw} {d b : Bool} {F : X.Modules} (hF : IsVB F r)
    {s : ∀ a : Fin Z.m, Fin r → Γ(F, h ⁻¹ᵁ (Z.U a).1)} (hL : IsLat Z h x d b F s) :
    IsLat Z (g ≫ h) x d b ((Scheme.Modules.pullback g).obj F)
      (fun a i => pullbackSections g F (Scheme.Hom.comp_preimage g h _).le (s a i)) := by
  haveI := hF.isQuasicoherent
  refine ⟨fun a => isFrame_pullS g _ (hL.frame a), ?_, ?_⟩
  · intro k _ w a a' φ φ' h1 h2 j
    have := hL.glue k (w ≫ g) a a' φ φ' (by rw [h1, Category.assoc]) (by rw [h2, Category.assoc]) j
    simp only [Category.assoc] at this ⊢
    convert this using 2 with i
    rw [coef_pullS]
    exact valF_appLE w g _ (by rw [Scheme.Hom.comp_preimage, Scheme.Hom.comp_preimage]; exact le_rfl) _
  · intro y w hw a φ hφ V e he hV cf v hv
    obtain ⟨V₁, e₁, hx, he₁⟩ := hF (g (w (IsLocalRing.closedPoint _)))
    have hV₁ : ⊤ ≤ (w ≫ g) ⁻¹ᵁ V₁ := top_le_of_closedPoint _ _ hx
    rw [hL.norm y (w ≫ g) (by rw [Category.assoc]; exact hw) a φ hφ V₁ e₁ he₁ hV₁ cf v hv]
    have hc : ∀ l i, valF (spMap (intO ↥y.C.S).subtype ≫ w ≫ g) _ (coef d he₁ (hL.frame a) l i) =
        valF (spMap (intO ↥y.C.S).subtype ≫ w) _ (coef d (isFrame_pullS g le_rfl he₁)
          (isFrame_pullS g (Scheme.Hom.comp_preimage g h _).le (hL.frame a)) l i) := by
      intro l i
      rw [coef_pullS g d le_rfl (Scheme.Hom.comp_preimage g h _).le he₁ (hL.frame a) l i, ← Category.assoc]
      exact (valF_appLE (spMap (intO ↥y.C.S).subtype ≫ w) g (U := V₁ ⊓ h ⁻¹ᵁ ↑(Z.U a))
        (U' := g ⁻¹ᵁ V₁ ⊓ (g ≫ h) ⁻¹ᵁ ↑(Z.U a)) _ (by rw [Scheme.Hom.comp_preimage]; exact le_rfl) _).symm
    simp only [← Category.assoc] at hc ⊢
    simp only [hc]
    exact (norm_coef_iff d he (isFrame_pullS g le_rfl he₁) _ _ w hV hV₁ cf).symm

end Lat

end GlobalTheory.ChainPts.PullHT

namespace GlobalTheory.ChainPts.PullHT

open GlobalTheory.VB (IsFrame IsVB)

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {B B₁ : Vert.Model O}

section Lat

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

theorem isEqLatPres_pull {Z : LocM.Mdl Y i₀} (g : Vert.Model.Hom B B₁) (h : B₁.X ⟶ Z.X) {r : ℕ}
    {x : Fin r → Letter Dw} {d : Bool} {P : EPres B₁ (𝓞 E)} (hP : IsEqLatPres Z h x d P) :
    IsEqLatPres Z (g.f ≫ h) x d (EPres.pull g P) := by
  obtain ⟨hr, s, h1, h2, h3⟩ := hP
  have vb' : IsVB P.E'.V r := hr ▸ P.vb'
  have vb : IsVB P.E.V r := hr ▸ P.vb
  haveI := vb'.isQuasicoherent
  refine ⟨hr, fun a i => pullbackSections g.f P.E'.V (Scheme.Hom.comp_preimage g.f h _).le (s a i), isLat_pull g.f h vb' h1, ?_, ?_⟩
  · have e : ∀ a i, ((EPres.pull g P).ψ.hom.app _ (pullbackSections g.f P.E'.V (Scheme.Hom.comp_preimage g.f h _).le (s a i))) =
        pullbackSections g.f P.E.V (Scheme.Hom.comp_preimage g.f h _).le (P.ψ.hom.app _ (s a i)) := fun a i =>
      pullback_map_app_pullbackSections g.f P.ψ.hom _ _
    simp only [e]
    exact isLat_pull g.f h vb h2
  · intro a i c
    change ((Scheme.Modules.pullback g.f).map (P.E'.ρ c : P.E'.V ⟶ P.E'.V)).app _ _ = _
    rw [pullback_map_app_pullbackSections, h3, pullbackSections_smul]
    congr 1
    rw [Scheme.Hom.comp_app]
    first
      | (erw [Scheme.Hom.appLE_eq_app]; rfl)
      | (simp only [Scheme.Hom.appLE]
         erw [show (homOfLE (le_refl (g.f ⁻¹ᵁ h ⁻¹ᵁ ↑(Z.U a)))).op = 𝟙 _ from rfl, CategoryTheory.Functor.map_id, Category.comp_id]
         rfl)

end Lat

end GlobalTheory.ChainPts.PullHT

namespace GlobalTheory.ChainPts.PullHT

open GlobalTheory.VB (IsFrame IsVB)

theorem isHTPair_pull : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p} (Z : GlobalTheory.LocM.Mdl Y i₀) {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (B₁ B : GlobalTheory.Vert.Model O) (g : GlobalTheory.Vert.Model.Hom B B₁) (h₁ : B₁.X ⟶ Z.X) {r : ℕ} (x : Fin r → Letter Dw) (lw oo : EPres B₁ (𝓞 E)), IsHTPair Z h₁ x lw oo → ∃ lw' oo' : EPres B (𝓞 E), IsHTPair Z (g.f ≫ h₁) x lw' oo' := by
  intro E _ _ _ H Dw Xo p W Y i₀ Z O _ _ _ B₁ B g h₁ r x lw oo hP
  obtain ⟨⟨π, wl, ⟨u, hu⟩, hw⟩, h1, h2⟩ := hP
  refine ⟨EPres.pull g lw, EPres.pull g oo, ⟨g.f.appTop π, (pullA g.f).map wl,
    ⟨Units.map g.f.appTop.hom.toMonoidHom u, ?_⟩, ?_⟩, isEqLatPres_pull g h₁ h1, isEqLatPres_pull g h₁ h2⟩
  · rw [Units.coe_map, ← map_pow, hu, map_mul, map_natCast]
    rfl
  · change (pullA g.f).map lw.ψ ≫ (pullA g.f).map wl = _
    rw [← Functor.map_comp, hw]
    apply Action.Hom.ext
    exact VB.pullback_map_smulHom g.f π

end GlobalTheory.ChainPts.PullHT

end
