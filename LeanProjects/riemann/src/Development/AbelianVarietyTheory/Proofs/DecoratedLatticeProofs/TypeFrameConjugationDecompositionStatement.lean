import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TypeFrameConjugationDecomposition
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemLevelIffSymmetricPositionEntryPattern
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnesRepresent
open ValuativeRel Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.type_frame_conjugation_decomposition : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (s κ : ℕ) (S : GlobalTheory.SymChain.SymData k s κ) (t : Type) [Fintype t] [DecidableEq t] (hc : 0 + (s + 1) = s + 1) (x : S.P.J), ∃ (a b : S.P.J) (γ : GL (GlobalTheory.StepData.XIx (Fin κ) t 0) k), (GlobalTheory.StepData.typeFrame S.ϖ (GlobalTheory.StepData.stdOrd (Fin κ) t 0 (s + 1) hc)).conj (GlobalTheory.StepData.reGL (GlobalTheory.StepData.ixZero (Fin κ ⊕ Fin (s + 1)) t) (a : GL (Fin κ ⊕ Fin (s + 1)) k)) ∈ GlobalTheory.RootEx.N k (GlobalTheory.StepData.XIx (Fin κ) t 0) (s + 1) (S.ρ + 1) ∧ (GlobalTheory.StepData.typeFrame S.ϖ (GlobalTheory.StepData.stdOrd (Fin κ) t 0 (s + 1) hc)).conj (GlobalTheory.StepData.reGL (GlobalTheory.StepData.ixZero (Fin κ ⊕ Fin (s + 1)) t) (b : GL (Fin κ ⊕ Fin (s + 1)) k)) = GlobalTheory.RootEx.embX (s + 1) γ ∧ GlobalTheory.StepData.MaxM (((a * b : S.P.J) : GL (Fin κ ⊕ Fin (s + 1)) k).val - (x : GL (Fin κ ⊕ Fin (s + 1)) k).val) := by
  first | exact @GlobalTheory.SymChain.SymData.exists_N_mul_embX_congr | exact GlobalTheory.SymChain.SymData.exists_N_mul_embX_congr | (intros; apply GlobalTheory.SymChain.SymData.exists_N_mul_embX_congr <;> assumption)
