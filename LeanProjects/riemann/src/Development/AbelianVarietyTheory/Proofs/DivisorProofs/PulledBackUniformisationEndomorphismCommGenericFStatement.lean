import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PulledBackUniformisationEndomorphismCommGenericF
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZHAbove
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationEndomorphismsToCompleteDvr
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkUInvariantUnderFieldEmbedding
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPelUnifPsiCoord
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PointsCarryCommonFlagSpectrumMapFieldExt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UwRQeIsNsmul
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.ArcPull

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pulledBack_uniformisationEndomorphism_comm_genericFibre : ∀ {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {I : Ideal R} {I' : Ideal R'} (g : R →+* R') (hg : Function.Injective g) {D : DegData R I} {D' : DegData R' I'} {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {A' : PolAV (Spec (CommRingCat.of (FractionRing R')))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (U' : UnifPre I' D' A' ((Over.pullback (specOf g)).obj G)) (gA : A'.A.left ⟶ A.A.left), IsGrpPullback A'.A A.A (spMap (fracMap hg)) gA → gA ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK R) = U'.gen.inv.left ≫ pullback.fst ((Over.pullback (specOf g)).obj G).hom (jK R') ≫ pullback.fst G.hom (specOf g) → ∀ (E : EndU U) (E' : EndU U'), E'.aG = (Over.pullback (specOf g)).map E.aG → E'.aA.left ≫ gA = gA ≫ E.aA.left := by
  first | exact @GlobalTheory.Poinc.AComm.pulled_end_comm | exact GlobalTheory.Poinc.AComm.pulled_end_comm | (intros; apply GlobalTheory.Poinc.AComm.pulled_end_comm <;> assumption)
