import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AmpleOnLocalizedModel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Models GlobalTheory.TorRef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ample_on_localized_model : FreeSt → ExtendSt → ExtAtSt → GlueSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Z : Model Xo c (algebraMap (𝓞 c.F) c.F)) (R : Type) [CommRing R] (a : 𝓞 c.F) (b : 𝓞 c.F →+* R) (ω : R →+* c.F) (C : Model Xo c ω) (m : ℕ), IsDedFrac ω → ω.comp b = algebraMap (𝓞 c.F) c.F → @IsLocalization.Away (𝓞 c.F) _ a R _ b.toAlgebra → 1 ≤ m → AmpAt C m → (∀ z : Z.X, ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ξ : Sp R' ⟶ Z.X) (t : SAB H (Sp R')) (_ : SABMap t Z.t ξ) (P : PELUnif (maximalIdeal R') t), IsCN R' ∧ ξ (closedPoint R') = z ∧ (Scheme.stalkClosedPointTo ξ).hom.Flat ∧ FineData P.D.toPre 1 ∧ FineData P.D.toPre (m ^ 2)) → Dominates Z C b := by
  first | exact @GlobalTheory.DomFine.dominates_of_fineData | exact GlobalTheory.DomFine.dominates_of_fineData | (intros; apply GlobalTheory.DomFine.dominates_of_fineData <;> assumption)
