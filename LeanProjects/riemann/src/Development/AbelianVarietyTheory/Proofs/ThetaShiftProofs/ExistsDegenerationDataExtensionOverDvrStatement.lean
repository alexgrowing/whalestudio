import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsDegenerationDataExtensionOverDvr
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ModelsAt
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_degenerationData_extension_over_dvr : Known → ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (Pv : Out.PolAV (Sp V)) (DK : Out.DegPre K) (φ : DK.P.A.left ⟶ Pv.A.left), IsPolFibre (algebraMap V K) Pv DK.P φ → ∃ (DV : Out.DegPre V) (p : Out.IsPullDeg (algebraMap V K) DV DK), DV.P = Pv ∧ HEq (prj p) φ ∧ ∀ (k : ℕ) (q' : Out.QkPt DK (FractionRing K) k), DK.TauBimult → ∃ q, GlobalTheory.ArcPull.IsPullQk p q q' := by
  first | exact @GlobalTheory.DvrDeg.exists_extension | exact GlobalTheory.DvrDeg.exists_extension | (intros; apply GlobalTheory.DvrDeg.exists_extension <;> assumption)
