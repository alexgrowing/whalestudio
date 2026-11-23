import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRigidifiedSymmetricLineBundle
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsTateZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsProjOverOfIsProjOverBase
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHeckeQuotientTriple
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
open CategoryTheory AlgebraicGeometry Set Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.ArInt GlobalTheory.TorsionForm GlobalTheory.ThetaRR
open GlobalTheory.LB (toMod)
open GlobalTheory.LieVB (omega)
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe (Fl Pt stdLat symMat tauU siegel symPart ChernIsFlat IsMetric InducesPolarisation cov)
open ReciprocityTheory.L2DbarEstimates (V)
open Filter Topology
open scoped ContDiff
open MonoidalCategory CartesianMonoidalCategory Limits
open GlobalTheory.CechPic (Pic cls lam)
open MonObj
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rigidified_symmetric_line_bundle : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] (M : LB A.left) (hM : M.IsLB), Out.Sym A M → ∃ (M' : LB A.left) (hM' : M'.IsLB), Out.Rigidified A M' ∧ Out.Sym A M' ∧ lam (cls M' hM') (fst A A) (snd A A) = lam (cls M hM) (fst A A) (snd A A) := by
  first | exact @GlobalTheory.RigidifyTwist.rigidified_sym_lam_twist | exact GlobalTheory.RigidifyTwist.rigidified_sym_lam_twist | (intros; apply GlobalTheory.RigidifyTwist.rigidified_sym_lam_twist <;> assumption)
