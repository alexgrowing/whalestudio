import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealAlongLocalSpecVanishingIdealComplEqSpan
import Development.AbelianVarietyTheory.Definitions.Divisors.IsMumfordFamOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc
open ReciprocityTheory.AnForm.R
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idealAlongLocalSpec_vanishingIdeal_compl_eq_span : ∀ (S : Scheme.{0}) (U : S.Opens) (R : Type) [CommRing R] [IsLocalRing R] (ξ : Sp R ⟶ S) (f : R), (Ideal.span {f}).IsRadical → (∀ p : Sp R, ξ p ∈ (U : Set S) ↔ f ∉ p.asIdeal) → (∀ I : Ideal (S.presheaf.stalk (ξ (closedPoint R))), I.IsRadical → (I.map (Scheme.stalkClosedPointTo ξ).hom).IsRadical) → idlAlong (Scheme.IdealSheafData.vanishingIdeal U.compl) ξ = Ideal.span {f} := by
  first | exact @GlobalTheory.PolDeg.idlAlong_vanishingIdeal_compl | exact GlobalTheory.PolDeg.idlAlong_vanishingIdeal_compl | (intros; apply GlobalTheory.PolDeg.idlAlong_vanishingIdeal_compl <;> assumption)
