import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TwistedHodgeCptCompare
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.TwTan
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_hodge_cpt_compare : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O O' : Type) [CommRing O] [CommRing O'] (β : O →+* c.F) (β' : O' →+* c.F) (Y : Model Xo c β) (Y' : Model Xo c β') (g : HostAut H) (Φ : Xo.X ≅ Xo.X) (n : SABMap (twistSAB Xo.univ.t g) Xo.univ.t Φ.hom) (S : Finset ℕ) (Ω Ω' : Type) [Field Ω] [Field Ω'] (K K' : Type) [Fintype K] [Fintype K'] (J : K → Type) (J' : K' → Type) [∀ k, Fintype (J k)] [∀ k, Fintype (J' k)] (y : (Σ k, J k) → Ω) (y' : (Σ k, J' k) → Ω') (A : HodgeCpt Y S y) (A' : HodgeCpt Y' S y') (Fl : A.Flag) (Fl' : A'.Flag) (ψ : A'.Ω₀ ≃+* A.Ω₀) (x₀ : Sp A.Ω₀ ⟶ Xo.XF c) (x₀' : Sp A'.Ω₀ ⟶ Xo.XF c), Mono (spMap β) → Mono (spMap β') → A.ξ₀ = x₀ ≫ Y.j → A'.ξ₀ = x₀' ≫ Y'.j → spMap ψ.toRingHom ≫ x₀' ≫ pullback.fst _ _ = x₀ ≫ pullback.fst _ _ ≫ Φ.hom → spMap ψ.toRingHom ≫ x₀' ≫ pullback.snd _ _ = x₀ ≫ pullback.snd _ _ → ∃ θ : Fl.Li₀ ≃+ Fl'.Li₀, (∀ (a : A'.Ω₀) e, θ (ψ a • e) = a • θ e) ∧ (∀ e, TwTan n Y Y' (Fl.M₀.pt e).left (spMap (dualMap ψ.toRingHom) ≫ (Fl'.M₀.pt (θ e)).left)) ∧ ∀ s s', labelEmb c s' = (labelEmb c s).comp g.s.toRingHom → ∀ e, e ∈ Fl.V₀ s ↔ θ e ∈ Fl'.V₀ s' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.LieTw.main | exact GlobalTheory.CompanionTheory.Ar.LieTw.main | (intros; apply GlobalTheory.CompanionTheory.Ar.LieTw.main <;> assumption)
