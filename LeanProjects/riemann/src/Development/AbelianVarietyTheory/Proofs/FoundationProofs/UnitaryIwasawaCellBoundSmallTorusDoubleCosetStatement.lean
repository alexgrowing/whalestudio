import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryIwasawaCellBoundSmallTorusDoubleCoset
import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeVecMemFixed
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAntiJFrame
open Formalism.UG GlobalTheory.PRep GlobalTheory.LFun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryIwasawaCell_bound_small_torusDoubleCoset : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q n : ℕ), IsUnramInv ϖ σ q → ∀ (ε κ : Fin (n / 2) → ℤ) (u k k₁ k₂ : GU σ n), (∀ i, |ε i| ≤ 1) → IsUnipU u → k ∈ KU σ n → k₁ ∈ KU σ n → k₂ ∈ KU σ n → tMat ϖ n (n / 2) κ * ((u : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * ((k : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = ((k₁ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * tMat ϖ n (n / 2) ε * ((k₂ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) → (∀ i, |κ i| ≤ 1) ∧ ∑ i, |κ i| ≤ ∑ i, |ε i| := by
  first | exact @GlobalTheory.LFun.CellBound.cell_bound | exact GlobalTheory.LFun.CellBound.cell_bound | (intros; apply GlobalTheory.LFun.CellBound.cell_bound <;> assumption)
