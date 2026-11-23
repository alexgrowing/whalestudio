import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EigenvalueProductMapsLetterLatticeOfConclusionsA
import Formalism.SharpRestriction.LevelLetterCocycles.UsedLocalConclusion
import Formalism.SharpRestriction.LevelLetterCocycles.LetterConditionGlobal
import Formalism.SharpRestriction.LevelLetterCocycles.CrystallineLiftingInputs
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.letterConditionGlobal_of_N1used : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), Formalism.MainNotions.DeltaInvariantLattices.DeltaInvariantNormBound D HW F Cm → Formalism.MainNotions.N.LetterConditionGlobal D HW F := by
  first | exact @GlobalTheory.PrimeSequence.eigenvalue_product_maps_letter_lattice_of_conclusions | exact GlobalTheory.PrimeSequence.eigenvalue_product_maps_letter_lattice_of_conclusions | (intros; apply GlobalTheory.PrimeSequence.eigenvalue_product_maps_letter_lattice_of_conclusions <;> assumption)
