import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymLevelChainTestFunctionAddRow
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.AllPositions
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symLevelChain_testFunction_add_row : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (s κ : ℕ) (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t], S.Pattern t → ∀ (j c : ℕ) (H : j + c = s) (q : Fin c), q.val + 1 ≤ S.ρ → ∀ (x : Matrix (XIx (Fin κ) t (j + 1) ⊕ Fin c) (XIx (Fin κ) t j ⊕ Fin (c + 1)) k), (∀ s', x (Sum.inr q) (Sum.inl s') = 0) → ∀ v : XIx (Fin κ) t j → k, (S.T t).Phi j c H (x + Matrix.of fun r s' => if r = Sum.inr q then Sum.elim v 0 s' else 0) = if ∀ s', valuation k ((((S.ϖ ^ (q.val + 1))⁻¹ : kˣ) : k) * v s') ≤ 1 then (S.T t).Phi j c H x else 0 := by
  first | exact @GlobalTheory.SymChain.RowShift.phi_add_row | exact GlobalTheory.SymChain.RowShift.phi_add_row | (intros; apply GlobalTheory.SymChain.RowShift.phi_add_row <;> assumption)
