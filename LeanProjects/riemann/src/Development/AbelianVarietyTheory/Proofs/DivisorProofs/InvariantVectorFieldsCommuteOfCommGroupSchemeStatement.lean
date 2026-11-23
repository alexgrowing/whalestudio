import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantVectorFieldsCommuteOfCommGroupScheme
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntDerApply
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.Heat GlobalTheory.FormalOrigin
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.invariantVectorFields_commute_of_commGroupScheme : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (v v' : TanM (𝟙 (Sp R)) G) (dd dd' : Fld G.left), IsInv G v dd → IsInv G v' dd' → ∀ O f, dd O (dd' O f) = dd' O (dd O f) := by
  first | exact @GlobalTheory.InvFieldComm.invField_comm | exact GlobalTheory.InvFieldComm.invField_comm | (intros; apply GlobalTheory.InvFieldComm.invField_comm <;> assumption)
