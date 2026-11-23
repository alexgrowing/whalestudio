import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.BlockTriangularOfSubOne
import Formalism.MirabolicMackeyTheory.MirabolicIsMackey
import CompanionTheory.AutomorphicTheory.MirabolicRestriction.MirabolicInduction.IndIrr
import CompanionTheory.AutomorphicTheory.MirabolicRestriction.MirabolicInduction.IndDim

noncomputable section

open GlobalTheory.FiniteGL Formalism.L2.Indef.Tree Formalism.EigenvalueLevelCeiling

namespace CompanionTheory.Mirab

variable {k : Type} [Field k] [Fintype k] (n : ℕ)

theorem mirabInduced_isIrreducible (ψ₀ : AddChar k ℂ) (hψ : ψ₀ ≠ 1) : (mirabInduced n ψ₀).IsIrreducible := by
  exact CompanionTheory.Mirab.Irr.mirabInduced_isIrreducible n ψ₀ hψ

theorem finrank_mirabInducedSpace_eq_index (ψ₀ : AddChar k ℂ) :
    Module.finrank ℂ (MirabInducedSpace n ψ₀) = (uniSub k n).index := by
  exact CompanionTheory.Mirab.Dim.finrank_mirabInducedSpace_eq_index n ψ₀

theorem index_uniSub : (uniSub k n).index = ∏ i ∈ Finset.Ico 1 (n + 1), (Fintype.card k ^ i - 1) := by
  exact CompanionTheory.Mirab.Dim.index_uniSub n

theorem finrank_mirabInducedSpace (ψ₀ : AddChar k ℂ) :
    Module.finrank ℂ (MirabInducedSpace n ψ₀) = ∏ i ∈ Finset.Ico 1 (n + 1), (Fintype.card k ^ i - 1) := by
  rw [finrank_mirabInducedSpace_eq_index, index_uniSub]

end CompanionTheory.Mirab
