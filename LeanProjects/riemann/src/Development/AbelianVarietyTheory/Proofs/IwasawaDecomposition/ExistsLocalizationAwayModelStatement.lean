import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalizationAwayModel
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsChartOf
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.Models
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_localization_away_model : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {R : Type} [CommRing R] {ω : R →+* c.F} (C : Model Xo c ω) (g : R), IsDedFrac ω → ω g ≠ 0 → ∃ (R' : Type) (_ : CommRing R') (e : R →+* R') (ω' : R' →+* c.F) (C' : Model Xo c ω') (v : C'.X ⟶ C.X), @IsLocalization.Away R _ g R' _ e.toAlgebra ∧ ω'.comp e = ω ∧ IsDedFrac ω' ∧ IsOpenImmersion v ∧ v ≫ C.s = C'.s ≫ spMap e ∧ Set.range v = C.s ⁻¹' {x | g ∉ x.asIdeal} ∧ C'.j ≫ v = C.j ∧ Nonempty (SABMap C'.t C.t v) := by
  first | exact @GlobalTheory.ModelRestrict.exists_restrict | exact GlobalTheory.ModelRestrict.exists_restrict | (intros; apply GlobalTheory.ModelRestrict.exists_restrict <;> assumption)
