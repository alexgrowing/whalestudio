import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleKernelTrivialOfSameImagePoint
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkBaseChange
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ProperRelAmpleKTrivOfFieldExtension
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmpleOfAmpleGeometricFibresAbelianScheme
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PolarisationExtendsOverDvrGoodReduction
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.KTrivOfKTrivNonemptyOpenNormalCharZero
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SurjectiveCubeBaseChange
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relAmple_kernelTrivial_of_same_image_point : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], QuasiCompact G.hom → IsSeparated G.hom → Smooth G.hom → ∀ (L : LB G.left), L.IsLB → ∀ (K₁ : Type) [Field K₁] (z : Sp K₁ ⟶ S), IsProper (pullback.snd G.hom z) → RelAmple ((Over.pullback z).obj G) (L.pull (pullback.fst G.hom z)) → KTriv ((Over.pullback z).obj G) (L.pull (pullback.fst G.hom z)) → ∀ (K : Type) [Field K] (x : Sp K ⟶ S), x (closedPoint K) = z (closedPoint K₁) → RelAmple ((Over.pullback x).obj G) (L.pull (pullback.fst G.hom x)) ∧ KTriv ((Over.pullback x).obj G) (L.pull (pullback.fst G.hom x)) := by
  first | exact @GlobalTheory.FibreTransfer.relAmple_kTriv_of_same_point | exact GlobalTheory.FibreTransfer.relAmple_kTriv_of_same_point | (intros; apply GlobalTheory.FibreTransfer.relAmple_kTriv_of_same_point <;> assumption)
