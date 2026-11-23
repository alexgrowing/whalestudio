import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntOfIsIntegral
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GenericSectionExtendsNormalStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationBaseChangeModels
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsIntegrallyClosedPowerSeries
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PullbackModelArcPeriodStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PullbackModelArcLimitStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef

namespace GlobalTheory.PolArcExtend

theorem powerSeries_props (O' : Type) [CommRing O'] [IsDomain O'] (ϖ : O') (h : IsArcBase O' ϖ) :
    ∃ (_ : IsLocalRing (PowerSeries O')), IsNoetherianRing (PowerSeries O') ∧ IsIntegrallyClosed (PowerSeries O') := by
  rcases h with ⟨hF, -⟩ | ⟨hD, -, -⟩
  · letI := hF.toField
    exact ⟨inferInstance, inferInstance, GlobalTheory.PowerSeriesNormal.isIntegrallyClosed_powerSeries O'⟩
  · exact ⟨inferInstance, inferInstance, GlobalTheory.PowerSeriesNormal.isIntegrallyClosed_powerSeries O'⟩

theorem spMap_jK' {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {g : R →+* R'}
    {gam : FractionRing R →+* FractionRing R'} (h : ∀ r, gam (algebraMap R _ r) = algebraMap R' _ (g r)) :
    spMap gam ≫ Out.jK R = Out.jK R' ≫ spMap g := by
  show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext (RingHom.ext h)

theorem extend : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
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
        ∃ χ : Sp (PowerSeries O') ⟶ Z.X, Out.jK (PowerSeries O') ≫ χ = x₀ ≫ Z.j := by
  intro E _ _ _ H D l Xo c p W hp hpW Z Y bV hbV f t m₁ m₂ hfs hgen huniv φ m BD hhom hpol O' _ _ _ b' ϖ a χ₀ hO hχ₀ x₀ hx₀
  obtain ⟨_, _, _⟩ := powerSeries_props O' ϖ hO
  have : CharZero (PowerSeries O') := charZero_of_injective_ringHom (PowerSeries.C_injective (R := O'))
  have := isProper_toroidalModel_structureMap Z
  have : CompactSpace Z.X := hpol.2.compactSpace
  have : QuasiSeparatedSpace Z.X := quasiSeparatedSpace_of_quasiSeparated Z.s
  have eF : spMap (algebraMap (𝓞 c.F) c.F) = spMap (c.V W).subtype ≫ spMap bV := by
    rw [← spMap_comp]
    congr 1
    ext x
    exact congrArg (fun y : c.F => (y : ℂ)) (hbV x).symm
  have hZs : x₀ ≫ Z.j ≫ Z.s = Out.jK (PowerSeries O') ≫ spMap (PowerSeries.C (R := O')) ≫ spMap b' ≫ spMap bV := by
    have hY : x₀ ≫ Y.j ≫ Y.s = Out.jK (PowerSeries O') ≫ spMap (PowerSeries.C (R := O')) ≫ spMap b' := by
      rw [← Category.assoc, ← hx₀, Category.assoc, hχ₀.1]
    rw [Model.j_s] at hY ⊢
    rw [eF]
    simp only [← Category.assoc] at hY ⊢
    rw [hY]
  obtain ⟨n, hn⟩ := GlobalTheory.T.pullback_model_arc_period E H D l Xo c p W hp hpW Z Y bV hbV f t m₁ m₂ hfs hgen huniv φ m BD hhom hpol O' b' ϖ a
    χ₀ hO hχ₀ x₀ hx₀
  obtain ⟨e, he, htr⟩ := GlobalTheory.T.pullback_model_arc_limit E H D l Xo c p W hp hpW Z Y bV hbV f t m₁ m₂ hfs hgen huniv φ m BD hhom hpol O' b' ϖ
    a χ₀ hO hχ₀ x₀ hx₀ n hn
  refine GlobalTheory.T.generic_section_extends_normal Z.X (polOf Z m BD) hpol.2.isLB (fun z => GlobalTheory.PolFin.exists_H0_of_isAmpleLB hpol.2 z) (PowerSeries O')
    (x₀ ≫ Z.j) e he fun V _ _ _ hV ψ gam hg => ?_
  have := hV.1
  obtain ⟨χ, hχ, -⟩ := val_exists Z.s (spMap gam ≫ x₀ ≫ Z.j)
    (spMap ψ ≫ spMap (PowerSeries.C (R := O')) ≫ spMap b' ≫ spMap bV) (by
      rw [Category.assoc, Category.assoc, hZs, ← Category.assoc (spMap gam), spMap_jK' hg, Category.assoc])
  exact ⟨χ, hχ.symm, htr V hV ψ gam hg χ hχ.symm⟩

end GlobalTheory.PolArcExtend
