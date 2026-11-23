import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsOriginBoxValueExponentLe
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasurableSetSetOfLe
open MeasureTheory ValuativeRel Matrix
open GlobalTheory.OriginBox GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abs_originBoxValueExponent_le : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (G : Grid k), 1 ≤ G.s → ∀ (a a' : ℤ) (N : ℕ), (∀ i j, i ≤ G.m → j ≤ G.m → G.rank (i, j) ≤ N) → |expo G a a'| ≤ 8 * ((G.m : ℤ) ^ 3 * (N : ℤ) ^ 2 * (|a| + |a'|)) := by
  first | exact @GlobalTheory.OriginBox.abs_expo_le | exact GlobalTheory.OriginBox.abs_expo_le | (intros; apply GlobalTheory.OriginBox.abs_expo_le <;> assumption)
