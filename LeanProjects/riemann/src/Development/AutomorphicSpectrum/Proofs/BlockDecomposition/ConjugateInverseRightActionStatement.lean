import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConjugateInverseRightAction
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.GelfandKazhdanDuality.IsCuspFormDualMap
open NumberField IsDedekindDomain Matrix Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair GlobalTheory.DiscSpec PositivityTheory.PRW.GKD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugate_inverse_right_action : ∀ {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}, ∀ (o : Op E a) (φ : Sm E a) (h1 : (fun g => star (φ.1 (invA E a g))) ∈ Sm E a) (h2 : (fun g => star ((act (invTOp o) φ).1 (invA E a g))) ∈ Sm E a), act o (⟨fun g => star (φ.1 (invA E a g)), h1⟩ : Sm E a) = ⟨fun g => star ((act (invTOp o) φ).1 (invA E a g)), h2⟩ := by
  first | exact @GlobalTheory.CompanionTheory.DualMapAct.act_dual | exact GlobalTheory.CompanionTheory.DualMapAct.act_dual | (intros; apply GlobalTheory.CompanionTheory.DualMapAct.act_dual <;> assumption)
