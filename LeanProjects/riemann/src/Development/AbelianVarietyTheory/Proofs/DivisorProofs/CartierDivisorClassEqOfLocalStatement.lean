import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartierDivisorClassEqOfLocal
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTriSelf
open CategoryTheory Limits AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.Vert GlobalTheory.TriFrame GlobalTheory.FlagCell
open GlobalTheory.Twist (resM)
open Formalism.MainNotions.DIV.Cons (intO SCF)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cartier_divisor_class_eq_of_local : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (B : Vert.Model O) (P P' : VertDiv B), (∀ x : B.X, ∃ (V : B.X.Opens) (i : P.M.ι) (j : P'.M.ι) (hi : V ≤ P.M.U i) (hj : V ≤ P'.M.U j) (u : Γ(B.X, V)ˣ), x ∈ V ∧ P'.eqn j (inf_le_inf_left B.gen hj) = resG B.X inf_le_right u.val * P.eqn i (inf_le_inf_left B.gen hi)) → P.cls = P'.cls := by
  first | exact @GlobalTheory.Vert.VertDiv.cls_eq_of_local_units | exact GlobalTheory.Vert.VertDiv.cls_eq_of_local_units | (intros; apply GlobalTheory.Vert.VertDiv.cls_eq_of_local_units <;> assumption)
