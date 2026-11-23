import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAdelicUnitaryTrivialOutsideSplitPlaceLocEq
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemMaxCompactOfTrivOutsideLocalIntegral
open NumberField ReciprocityTheory.Aut
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_adelicUnitary_trivialOutside_splitPlace_loc_eq : ∀ {L : Type} [Field L] [NumberField L] [IsCMField L] (n : ℕ) (s : ReciprocityTheory.Aut.SplitPlace L) (M : GL (Fin n) (s.v.adicCompletion (NumberField.maximalRealSubfield L))), ∃ x : Formalism.AUTREP.GAf L n, ReciprocityTheory.Aut.TrivOutside {s.v} x ∧ s.loc n x = M := by
  first | exact @GlobalTheory.SplitLift.exists_trivOutside_loc_eq | exact GlobalTheory.SplitLift.exists_trivOutside_loc_eq | (intros; apply GlobalTheory.SplitLift.exists_trivOutside_loc_eq <;> assumption)
