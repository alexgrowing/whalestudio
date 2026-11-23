import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RelativeAmpleCanonicalTrivialLocal
import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relative_ample_canonical_trivial_local : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (O : Type) [CommRing O] [IsDomain O] [IsLocalRing O] [IsNoetherianRing O] [CharZero O], IsIntegrallyClosed O → ∀ (t : SAB H (Sp O)), IsProper t.G.hom → GlobalTheory.LN.PolAt t (Out.jK O) → Out.RelAmple t.G t.PP.L ∧ Out.KTriv t.G t.PP.L := by
  first | exact @GlobalTheory.PolLocal.relAmple_kTriv_of_polAt_generic | exact GlobalTheory.PolLocal.relAmple_kTriv_of_polAt_generic | (intros; apply GlobalTheory.PolLocal.relAmple_kTriv_of_polAt_generic <;> assumption)
