import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGeometricValuesIsoOfIdentificationDvr
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.ThetaTowerRecognition
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIsFib
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_geometric_values_iso_of_identification_dvr : Laws → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (D D' : DegPre V) (e : IsPullDeg (RingHom.id V) D D') (F : Type) [Field F] [Algebra (FractionRing V) F] (N N' : NumD F) (ν : NumOf D F N) (ν' : NumOf D' F N'), ∃ J : NumD.Iso N N', GeoIso ν ν' J.toIso ∧ ∀ (k : ℕ) (p : QkPt D F k) (p' : QkPt D' F k) (q : N.QT k) (q' : N'.QT k), ν.QPt p q → ν'.QPt p' q' → GlobalTheory.IndefiniteRowSideFullHecke.ThetaTowerRecognition.Carries e p p' → q'.1.1.toAdd = J.e q.1.1.toAdd ∧ J.Rel q.1.2 q'.1.2 := by
  first | exact @GlobalTheory.IdentifiedValues.exists_geoIso_rel | exact GlobalTheory.IdentifiedValues.exists_geoIso_rel | (intros; apply GlobalTheory.IdentifiedValues.exists_geoIso_rel <;> assumption)
