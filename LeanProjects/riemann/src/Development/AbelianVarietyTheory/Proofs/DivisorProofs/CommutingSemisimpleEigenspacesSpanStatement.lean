import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutingSemisimpleEigenspacesSpan
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SandwichMaps
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.commuting_semisimple_eigenspaces_span : ∀ (C : Type) [Field C] [IsAlgClosed C] (V : Type) [AddCommGroup V] [Module C V] [FiniteDimensional C V] (I : Type) (T : I → Module.End C V), (∀ a b, Commute (T a) (T b)) → (∀ a, ∃ f : Polynomial C, f.Separable ∧ Polynomial.aeval (T a) f = 0) → (⨆ χ : I → C, ⨅ a : I, Module.End.eigenspace (T a) (χ a)) = ⊤ := by
  first | exact @GlobalTheory.iSup_jointEigenspace_eq_top_of_separable | exact GlobalTheory.iSup_jointEigenspace_eq_top_of_separable | (intros; apply GlobalTheory.iSup_jointEigenspace_eq_top_of_separable <;> assumption)
