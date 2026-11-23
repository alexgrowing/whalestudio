import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviBlockRepEquivFirst
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GeometricLemmaFiltration
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BernsteinUnitaryProductIrreducible
open GlobalTheory.PRep GlobalTheory.SmGL Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levi_block_rep_equiv_first : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {m : Type} [Fintype m] [DecidableEq m] (b : SizeMatrix (Two (Fin 1) m) (Two (Fin 1) m)),
    b.1 false true = 0 → b.1 true false = 0 →
    ∀ {W : Type} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (Levi k (Two (Fin 1) m)) W), IsSmooth ρ →
    ∃ (f : ∀ i, (Σ j, Fin (b.1 i j)) ≃ Two (Fin 1) m i) (g : ∀ j, (Σ i, Fin (b.1 i j)) ≃ Two (Fin 1) m j),
      Nonempty ((cellFunctor f g ρ).Equiv ρ) := by
  first | exact @GlobalTheory.DiagCell.cellFunctor_diag_equiv | exact GlobalTheory.DiagCell.cellFunctor_diag_equiv | (intros; apply GlobalTheory.DiagCell.cellFunctor_diag_equiv <;> assumption)
