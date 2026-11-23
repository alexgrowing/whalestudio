import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleCubicalLineBundle
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_symmetric_ample_cubical_lineBundle_abelianVariety : ∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B], IsAbelianScheme B → ∃ L : LB B.left, GlobalTheory.SS.AmpleCub B L := by
  first | exact @GlobalTheory.SS.exists_ampleCub_of_isAbelianScheme | exact GlobalTheory.SS.exists_ampleCub_of_isAbelianScheme | (intros; apply GlobalTheory.SS.exists_ampleCub_of_isAbelianScheme <;> assumption)
