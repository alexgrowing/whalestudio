import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PowerSeriesArcAbelianLocus
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntOfIsIntegral
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.power_series_arc_abelian_locus : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (W : ValuationSubring ℂ) (Y : Model Xo c (c.V W).subtype) (O' : Type) [CommRing O'] [IsDomain O']
    [CharZero O'] (b' : c.V W →+* O') (χ₀ : Sp (PowerSeries O') ⟶ Y.X),
    χ₀ ≫ Y.s = spMap (PowerSeries.C (R := O')) ≫ spMap b' →
    (∀ x : Sp (PowerSeries O'), χ₀ x ∈ abLocus Y.t.G ↔ PowerSeries.X ∉ x.asIdeal) →
    ∃ x₀ : Sp (FractionRing (PowerSeries O')) ⟶ Xo.XF c, Out.jK (PowerSeries O') ≫ χ₀ = x₀ ≫ Y.j := by
  first | exact @GlobalTheory.PolArc.generic_factors_open | exact GlobalTheory.PolArc.generic_factors_open | (intros; apply GlobalTheory.PolArc.generic_factors_open <;> assumption)
