import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ArcDataPsiValuationEqHalfForm
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsFrameIff
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.LN GlobalTheory.Ex GlobalTheory.OneBasis
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arcData_psi_valuation_eq_half_form : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β), ∀ (O' : Type) [CommRing O'] [IsDomain O'] (b : O →+* O') (a : ArcIn D l β O' b) (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] (f : O' →+* W) (u : W) (χ : Sp W ⟶ Y.X), Function.Injective f → Y.HasArcData a (maximalIdeal W) f u χ → ∃ (t : SAB H (Sp W)) (_ : SABMap t Y.t χ) (P : PELUnif (maximalIdeal W) t) (e : a.D₀.X ≃+ P.D.toPre.X), ∀ (ϖ : W) (Q : P.D.toPre.X → ℤ) (w : ℕ), Irreducible ϖ → QForm.IsQ P.D.toPre ϖ Q → HasVal ϖ (algebraMap W (FractionRing W) u) w → ∀ y, Q (e y) = w * (a.be y y / 2) := by
  first | exact @GlobalTheory.ArcPsiVal.q_eq_of_hasArcData | exact GlobalTheory.ArcPsiVal.q_eq_of_hasArcData | (intros; apply GlobalTheory.ArcPsiVal.q_eq_of_hasArcData <;> assumption)
