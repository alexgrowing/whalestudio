import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSignsMatchBranchingCoordinateEquiv
import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ProjExists
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_signsMatchBranchingCoordinate_equiv : ∀ {n : ℕ} (ε : Fin (n + 1) → Bool) (ε' : Fin n → Bool), (Finset.univ.filter fun a => ε a = false).card = (Finset.univ.filter fun i => ε' i = false).card → ∃ e : Option (Fin n) ≃ Fin (n + 1), GlobalTheory.SepReal.Signs e ε ε' := by
  first | exact @GlobalTheory.SepReal.exists_signs_equiv | exact GlobalTheory.SepReal.exists_signs_equiv | (intros; apply GlobalTheory.SepReal.exists_signs_equiv <;> assumption)
