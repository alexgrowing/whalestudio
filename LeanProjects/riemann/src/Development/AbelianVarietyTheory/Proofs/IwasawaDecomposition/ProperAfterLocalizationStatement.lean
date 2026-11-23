import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ProperAfterLocalization
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpansAt
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj GlobalTheory.RayEv
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.proper_after_localization : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [CharZero R], IsIntegrallyClosed R → ∀ (t : SAB H (Sp R)), GlobalTheory.LN.PolAt t (jK R) → ∀ (C : Type) [Field C] (g : R →+* C), GlobalTheory.LN.PolAt t (spMap g) → ∃ r : R, g r ≠ 0 ∧ ∃ (t' : SAB H (Sp (Localization.Away r))) (_ : SABMap t' t (spMap (algebraMap R (Localization.Away r)))), IsProper t'.G.hom ∧ RelAmple t'.G t'.PP.L ∧ KTriv t'.G t'.PP.L := by
  first | exact @GlobalTheory.PolNear.exists_near | exact GlobalTheory.PolNear.exists_near | (intros; apply GlobalTheory.PolNear.exists_near <;> assumption)
