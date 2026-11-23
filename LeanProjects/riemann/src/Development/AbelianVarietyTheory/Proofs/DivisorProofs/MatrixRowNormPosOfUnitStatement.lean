import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixRowNormPosOfUnit
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTriSelf
open CategoryTheory Limits AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.Vert GlobalTheory.TriFrame GlobalTheory.FlagCell
open GlobalTheory.Twist (resM)
open Formalism.MainNotions.DIV.Cons (intO SCF)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matrix_row_norm_pos_of_unit : ∀ (C : Type) [NontriviallyNormedField C] (r : ℕ) (M : Matrix (Fin r) (Fin r) C), IsUnit M → ∀ i, 0 < matNorm M i := by
  first | exact @GlobalTheory.TriFrame.matNorm_pos_of_isUnit | exact GlobalTheory.TriFrame.matNorm_pos_of_isUnit | (intros; apply GlobalTheory.TriFrame.matNorm_pos_of_isUnit <;> assumption)
