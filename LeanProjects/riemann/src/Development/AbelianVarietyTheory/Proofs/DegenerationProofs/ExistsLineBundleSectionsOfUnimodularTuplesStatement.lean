import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLineBundleSectionsOfUnimodularTuples
import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnitCharts
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsAffineOpenNonzeroLocusOfUniversallyClosed
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lineBundle_sections_of_unimodular_tuples : ∀ (X : Scheme.{0}) (A J : Type) (V : A → X.Opens) (t : ∀ a, J → Γ(X, V a)), (∀ a, V a ≤ ⨆ i, X.basicOpen (t a i)) → (∀ a a' i j, resG X (inf_le_left : V a ⊓ V a' ≤ V a) (t a i) * resG X (inf_le_right : V a ⊓ V a' ≤ V a') (t a' j) = resG X (inf_le_left : V a ⊓ V a' ≤ V a) (t a j) * resG X (inf_le_right : V a ⊓ V a' ≤ V a') (t a' i)) → ∃ (g : ∀ a a', Γ(X, V a ⊓ V a')ˣ) (T : J → LB.Sec (⟨A, V, g⟩ : LB X)), ∀ i a, (T i).f a = t a i := by
  first | exact @GlobalTheory.TupleGlue.exists_sections | exact GlobalTheory.TupleGlue.exists_sections | (intros; apply GlobalTheory.TupleGlue.exists_sections <;> assumption)
