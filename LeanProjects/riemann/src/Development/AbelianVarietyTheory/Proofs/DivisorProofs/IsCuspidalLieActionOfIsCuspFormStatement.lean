import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCuspidalLieActionOfIsCuspForm
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
open NumberField GlobalTheory.CuspRep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCuspidal_lieAction_of_isCuspForm : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (X : GlobalTheory.CuspRep.Lie E a) (φ : GlobalTheory.CuspRep.Sm E a), GlobalTheory.CuspRep.IsCuspForm φ → GlobalTheory.CuspRep.IsCuspidal (GlobalTheory.CuspRep.lie E a X φ).1 := by
  first | exact @GlobalTheory.CuspRep.isCuspidal_lie_of_isCuspForm | exact GlobalTheory.CuspRep.isCuspidal_lie_of_isCuspForm | (intros; apply GlobalTheory.CuspRep.isCuspidal_lie_of_isCuspForm <;> assumption)
