import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteGroupSchemeStalkLengthConstant
import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.ChainOfKernelsUnique
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_group_scheme_stalk_length_constant : ∀ (k : Type) [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G], IsFinite G.hom → ∀ x x' : G.left, Module.length (G.left.presheaf.stalk x) (G.left.presheaf.stalk x) = Module.length (G.left.presheaf.stalk x') (G.left.presheaf.stalk x') := by
  first | (exact @GlobalTheory.FiniteGroupSchemeLength.length_stalk_eq) | (exact GlobalTheory.FiniteGroupSchemeLength.length_stalk_eq) | (intros; apply GlobalTheory.FiniteGroupSchemeLength.length_stalk_eq  <;> assumption)
