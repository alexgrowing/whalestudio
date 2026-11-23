import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsoOfSubbundleSameRank
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTriSelf
open CategoryTheory Limits AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.Vert GlobalTheory.TriFrame GlobalTheory.FlagCell
open GlobalTheory.Twist (resM)
open Formalism.MainNotions.DIV.Cons (intO SCF)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iso_of_subbundle_same_rank : ∀ (X : Scheme.{0}) [IsIntegral X] (G G' E : X.Modules) (n : ℕ) (i : G ⟶ E) (a : G' ⟶ G), IsVB G n → IsVB G' n → Mono i → IsSubbundle (a ≫ i) → IsIso a := by
  first | exact @GlobalTheory.TriFrame.isIso_of_isSubbundle_comp | exact GlobalTheory.TriFrame.isIso_of_isSubbundle_comp | (intros; apply GlobalTheory.TriFrame.isIso_of_isSubbundle_comp <;> assumption)
