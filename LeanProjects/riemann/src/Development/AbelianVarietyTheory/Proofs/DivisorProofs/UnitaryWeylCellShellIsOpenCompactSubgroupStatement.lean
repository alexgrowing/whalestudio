import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryWeylCellShellIsOpenCompactSubgroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConvUAbsU
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemShellUIffDepth
open MeasureTheory GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.WeylCell Formalism.UG GlobalTheory.WeylCell.WeylUnipotentShell
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryWeylCellShell_isOpenCompactSubgroup : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L)
    (σ : L →+* L) (q : ℕ), IsUnramInv ϖ σ q →
    ∀ (n : ℕ) (k : Fin (n / 2)), ¬ k.val + 1 < n / 2 → ¬ Even n →
    ∀ y : GU σ n, y ∈ KU σ n → IsWeylRep (simpleU k) (y : GL (Fin n) L) →
    (∀ j : ℤ, IsOpen (shellU k y j) ∧ IsCompact (shellU k y j) ∧ (1 : cellU y) ∈ shellU k y j ∧
      (∀ u v : cellU y, u ∈ shellU k y j → v ∈ shellU k y j → u * v ∈ shellU k y j) ∧
      (∀ u : cellU y, u ∈ shellU k y j → u⁻¹ ∈ shellU k y j)) ∧
    shellU k y 0 = (((KU σ n).subgroupOf (cellU y) : Subgroup (cellU y)) : Set (cellU y)) := by
  first | exact @GlobalTheory.WeylCell.WeylUnipotentShell.shellU_open_compact_subgroup | exact GlobalTheory.WeylCell.WeylUnipotentShell.shellU_open_compact_subgroup | (intros; apply GlobalTheory.WeylCell.WeylUnipotentShell.shellU_open_compact_subgroup <;> assumption)
