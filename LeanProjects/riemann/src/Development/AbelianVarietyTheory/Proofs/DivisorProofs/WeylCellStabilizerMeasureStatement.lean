import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeylCellStabilizerMeasure
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConvUAbsU
open MeasureTheory GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.WeylCell Formalism.UG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weyl_cell_stabilizer_measure : ∀ (L : Type) [Field L] [CharZero L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L]
    (ϖ : L) (σ : L →+* L) (q : ℕ), IsUnramInv ϖ σ q → ∀ (n : ℕ) (k : Fin (n / 2)), ¬ k.val + 1 < n / 2 →
    Even n → ∀ (y : GU σ n), y ∈ KU σ n → IsWeylRep (simpleU k) (y : GL (Fin n) L) →
    ∀ [MeasurableSpace (cellU y)] [BorelSpace (cellU y)] (μ : Measure (cellU y)) [μ.IsHaarMeasure],
    μ ((KU σ n).subgroupOf (cellU y)) = 1 → ∀ (j : ℤ),
    MeasurableSet {u : cellU y | Valued.v ((((u : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (lo k) (lo k).rev) ≤
        ((Multiplicative.ofAdd j : Multiplicative ℤ) : WithZero (Multiplicative ℤ))} ∧
    μ {u : cellU y | Valued.v ((((u : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (lo k) (lo k).rev) ≤
        ((Multiplicative.ofAdd j : Multiplicative ℤ) : WithZero (Multiplicative ℤ))} = (q : ENNReal) ^ j := by
  first | exact @GlobalTheory.ShellU.shell_measure | exact GlobalTheory.ShellU.shell_measure | (intros; apply GlobalTheory.ShellU.shell_measure <;> assumption)
