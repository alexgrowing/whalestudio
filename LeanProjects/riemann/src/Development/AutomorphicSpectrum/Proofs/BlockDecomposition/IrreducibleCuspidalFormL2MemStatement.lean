import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IrreducibleCuspidalFormL2Mem
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsFinitePartOfBot
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.irreducible_cuspidal_form_l2_mem : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (H : Submodule ℂ (L2 (latticeGL E a) μ)), H ≤ L2cusp μ → IsIrredSubrep (R (latticeGL E a) μ) H → ∀ W : Submodule ℂ (Sm E a), IsStable W → (∀ φ ∈ W, IsAutForm φ ∧ ∃ h : MemL2Quotient (latticeGL E a) μ φ.1, h.toL2 ∈ H) → (classes W μ).topologicalClosure = H → ∀ φ : Sm E a, IsAutForm φ → ∀ h : MemL2Quotient (latticeGL E a) μ φ.1, h.toL2 ∈ H → φ ∈ W := by
  first | exact @GlobalTheory.CompanionTheory.IrredMod.mem_of_toL2_mem | exact GlobalTheory.CompanionTheory.IrredMod.mem_of_toL2_mem | (intros; apply GlobalTheory.CompanionTheory.IrredMod.mem_of_toL2_mem <;> assumption)
