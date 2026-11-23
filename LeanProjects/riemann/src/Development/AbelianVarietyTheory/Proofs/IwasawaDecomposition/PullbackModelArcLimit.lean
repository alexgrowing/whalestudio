import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntOfIsIntegral
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GenericSectionExtendsNormalStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExtAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PullbackModelArcPolarizationStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GeneratorExtendsTensorStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GeneratorExtendsPowerStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdealAlongDvrArcsStatement
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef

namespace GlobalTheory.TraitGen

theorem exists_polGen_extends : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits →
    ∀ (Z : Model Xo c (algebraMap (𝓞 c.F) c.F)) (Y : Model Xo c (c.V W).subtype) (bV : 𝓞 c.F →+* c.V W)
    (hbV : ∀ x, ((bV x : c.V W) : c.F) = (x : c.F))
    (f : pullback Z.s (spMap bV) ⟶ Y.X) (t : SAB H (pullback Z.s (spMap bV)))
    (m₁ : SABMap t Z.t (pullback.fst Z.s (spMap bV))) (m₂ : SABMap t Y.t f),
    f ≫ Y.s = pullback.snd Z.s (spMap bV) →
    (∀ a : Xo.XF c ⟶ pullback Z.s (spMap bV), a ≫ pullback.fst Z.s (spMap bV) = Z.j → a ≫ f = Y.j) →
    (∀ (T : Scheme.{0}) (g : T ⟶ t.G.left) (g₁ : T ⟶ Z.oF.t.G.left) (g₂ : T ⟶ Y.oF.t.G.left),
      g ≫ m₁.φ = g₁ ≫ Z.m.φ → g₁ ≫ Z.m0.toSABMap.φ = g₂ ≫ Y.m0.toSABMap.φ → g₁ ≫ Z.oF.t.G.hom = g₂ ≫ Y.oF.t.G.hom →
      g ≫ m₂.φ = g₂ ≫ Y.m.φ) →
    ∀ (φ : InvFun (𝓞 E)) (m : ℕ) (BD : GlobalTheory.EffCartierData Z.X),
      (∀ (n : ℕ) (k : ℕ) (B : (Fin n → 𝓞 E) → (Fin n → 𝓞 E) → ℝ), φ.toFun n (fun a b => k * B a b) = k * φ.toFun n B) →
      IsPol φ m Z BD →
      ∀ (O' : Type) [CommRing O'] [IsDomain O'] [CharZero O'] (b' : c.V W →+* O') (ϖ : O')
        (a : ArcIn D l (algebraMap (𝓞 c.F) c.F) O' (b'.comp bV)) (χ₀ : Sp (PowerSeries O') ⟶ Y.X),
        IsArcBase O' ϖ → IsArcChart Y (GlobalTheory.PolArc.moveV bV hbV b' a) ϖ χ₀ →
        ∀ x₀ : Sp (FractionRing (PowerSeries O')) ⟶ Xo.XF c, Out.jK (PowerSeries O') ≫ χ₀ = x₀ ≫ Y.j →
        ∀ n : ℕ, (∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDvr V →
    ∀ (ψ : PowerSeries O' →+* V) (gam : FractionRing (PowerSeries O') →+* FractionRing V),
    (∀ r, gam (algebraMap (PowerSeries O') _ r) = algebraMap V _ (ψ r)) →
    ∀ χ : Sp V ⟶ Z.X, spMap gam ≫ x₀ ≫ Z.j = Out.jK V ≫ χ → GlobalTheory.LocM.idlAlong BD.idealSheaf χ = Ideal.span {ψ PowerSeries.X ^ n}) →
  ∃ e : LB.Gen ((polOf Z m BD).pull (x₀ ≫ Z.j)), e.IsGen ∧
  ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDvr V →
    ∀ (ψ : PowerSeries O' →+* V) (gam : FractionRing (PowerSeries O') →+* FractionRing V),
    (∀ r, gam (algebraMap (PowerSeries O') _ r) = algebraMap V _ (ψ r)) →
    ∀ χ : Sp V ⟶ Z.X, spMap gam ≫ x₀ ≫ Z.j = Out.jK V ≫ χ → ∃ e' : LB.Gen ((polOf Z m BD).pull χ), e'.IsGen ∧
      ∀ z J, ReciprocityTheory.ChartRestriction.G.Geo.Tor.Good (polOf Z m BD) z J →
        ReciprocityTheory.ChartRestriction.G.Geo.Tor.val (L := polOf Z m BD) (φ := fun _ : PUnit => x₀ ≫ Z.j) (ε := fun _ => 1) e (spMap gam) z J =
        ReciprocityTheory.ChartRestriction.G.Geo.Tor.val (L := polOf Z m BD) (φ := fun _ : PUnit => χ) (ε := fun _ => 1) e' (Out.jK V) z J := by
  intro E _ _ _ H D l Xo c p W hp hW Z Y bV hbV f t m₁ m₂ hf hj huniv φ m BD hhom hpol O' _ _ _ b' ϖ a χ₀ hB hC x₀ hx₀ n hn
  obtain ⟨e₁, he₁, hx₁⟩ := GlobalTheory.T.pullback_model_arc_polarization E H D l Xo c p W hp hW Z Y bV hbV f t m₁ m₂ hf hj huniv O' b' ϖ a χ₀ hB hC x₀ hx₀
  obtain ⟨e₂, he₂, hx₂⟩ := GlobalTheory.T.generator_extends_power _ _ _ _ e₁ m he₁ hx₁
  obtain ⟨e₃, he₃, hx₃⟩ := GlobalTheory.T.ideal_along_dvr_arcs Z.X BD (PowerSeries O') PowerSeries.X PowerSeries.X_ne_zero (x₀ ≫ Z.j) n hn
  obtain ⟨e, he, hx⟩ := GlobalTheory.T.generator_extends_tensor _ _ _ _ _ e₂ e₃ he₂ he₃ hx₂ hx₃
  exact ⟨e, he, hx⟩

end GlobalTheory.TraitGen
