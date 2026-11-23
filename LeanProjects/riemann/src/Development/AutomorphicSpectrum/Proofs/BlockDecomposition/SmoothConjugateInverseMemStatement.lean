import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothConjugateInverseMem
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.GelfandKazhdanDuality.IsCuspFormDualMap
open NumberField IsDedekindDomain Matrix Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair GlobalTheory.DiscSpec PositivityTheory.PRW.GKD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_conjugate_inverse_mem : ∀ {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}, ∀ {φ : GA E a → ℂ}, φ ∈ Sm E a → (fun g => star (φ (invA E a g))) ∈ Sm E a := by
  first | exact @GlobalTheory.CompanionTheory.DualSm.conj_invA_mem_Sm | exact GlobalTheory.CompanionTheory.DualSm.conj_invA_mem_Sm | (intros; apply GlobalTheory.CompanionTheory.DualSm.conj_invA_mem_Sm <;> assumption)
