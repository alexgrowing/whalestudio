import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixWeightedPairBundleRigidifiedAmple
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMonHomProdPow
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc GlobalTheory.ActFin
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matrixWeightedPairBundle_rigidified_ample : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (Q : LB (A ⊗ A).left), QHyp A Q → ∀ (r : ℕ) (W : Matrix (Fin r) (Fin r) ℤ), ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → IsAbelianScheme (Out.powObj A r) ∧ (formLB A Q (Out.powPr A (n := r)) W).IsLB ∧ Out.Rigidified (Out.powObj A r) (formLB A Q (Out.powPr A (n := r)) W) ∧ Out.RelAmple (Out.powObj A r) (formLB A Q (Out.powPr A (n := r)) W) := by
  first | (exact @GlobalTheory.PowFormProps.formLB_props) | (exact GlobalTheory.PowFormProps.formLB_props) | (intros; apply GlobalTheory.PowFormProps.formLB_props  <;> assumption)
