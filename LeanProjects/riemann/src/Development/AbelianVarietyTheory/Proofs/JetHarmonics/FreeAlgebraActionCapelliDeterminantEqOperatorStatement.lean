import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FreeAlgebraActionCapelliDeterminantEqOperator
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.RealPlaceAnalysis.StatementE
import Formalism.RealPlaceAnalysis.StatementKT
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.freeAlgebraAction_capelliDeterminant_eq_operator : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (S : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ S), (∀ a b (v : S), ((E a b v : S) : H) = PI.DSInfCharCap.dsigC ε σ (PI.DSInfCharCap.unitM (a, b)) v) → ∀ (u : ℂ) (v : S), PI.DSInfCharCap.actU ε σ (Formalism.REAL.qdet (PI.DSInfCharCap.Egl n) u) v = ((Formalism.REAL.qdet E u v : S) : H) := by
  first | exact @GlobalTheory.CapelliFreeAction.actU_qdet | exact GlobalTheory.CapelliFreeAction.actU_qdet | (intros; apply GlobalTheory.CapelliFreeAction.actU_qdet <;> assumption)
