import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GradedPieceFrameOfFlag
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTriSelf
open CategoryTheory Limits AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.Vert GlobalTheory.TriFrame GlobalTheory.FlagCell
open GlobalTheory.Twist (resM)
open Formalism.MainNotions.DIV.Cons (intO SCF)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.graded_piece_frame_of_flag : ∀ (X : Scheme.{0}) (F : X.Modules) (r : ℕ) (fl : Vert.Flag F r) (V : X.Opens) (e : Fin r → Γ(F, V)), Spans fl V e → ∀ (i : Fin r) (t : Γ(fl.F i.succ, V)), (fl.ι i.succ).app V t = e i → IsFrame fun _ : Fin 1 => (fl.π i).app V t := by
  first | exact @GlobalTheory.FlagCell.isFrame_π_of_spans | exact GlobalTheory.FlagCell.isFrame_π_of_spans | (intros; apply GlobalTheory.FlagCell.isFrame_π_of_spans <;> assumption)
