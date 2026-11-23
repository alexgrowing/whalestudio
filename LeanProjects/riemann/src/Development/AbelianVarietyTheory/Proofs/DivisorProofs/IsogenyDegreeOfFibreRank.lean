import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarMeasureProdOfAddGroups
import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.ChainOfKernelsUnique
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isogeny_degree_of_fibre_rank : ∀ (k : Type) [Field k] [IsAlgClosed k] (A : Over (Sp k)) [GrpObj A], IsAbelianScheme A →
    ∀ (φ : A ⟶ A), IsMonHom φ → IsFinite φ.left → ∀ d : ℕ,
    φ.left.finrank ((1 : Over.mk (𝟙 (Sp k)) ⟶ A).left (IsLocalRing.closedPoint k)) = d →
    GlobalTheory.IwLevel.IsIsogDeg φ d := by
  first | (exact @GlobalTheory.IwLevel.isIsogDeg_of_isFinite_of_finrank_origin) | (exact GlobalTheory.IwLevel.isIsogDeg_of_isFinite_of_finrank_origin) | (intros; apply GlobalTheory.IwLevel.isIsogDeg_of_isFinite_of_finrank_origin <;> assumption)
