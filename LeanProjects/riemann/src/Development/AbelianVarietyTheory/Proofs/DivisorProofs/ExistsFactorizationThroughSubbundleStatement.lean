import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorizationThroughSubbundle
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTriSelf
open CategoryTheory Limits AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.Vert GlobalTheory.TriFrame GlobalTheory.FlagCell
open GlobalTheory.Twist (resM)
open Formalism.MainNotions.DIV.Cons (intO SCF)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_factorization_through_subbundle : ∀ (X : Scheme.{0}) [IsIntegral X] (A : X.Opens) (G G' E : X.Modules) (i : G ⟶ E) (f : G' ⟶ E) (n : ℕ) (t : Fin n → Γ(G', A)), genericPoint X ∈ A → IsSubbundle i → IsFrame t → (∀ j, ∃ u : Γ(G, A), i.app A u = f.app A (t j)) → ∃ a : G' ⟶ G, a ≫ i = f := by
  first | exact @GlobalTheory.SubLift.factor_of_frame | exact GlobalTheory.SubLift.factor_of_frame | (intros; apply GlobalTheory.SubLift.factor_of_frame <;> assumption)
