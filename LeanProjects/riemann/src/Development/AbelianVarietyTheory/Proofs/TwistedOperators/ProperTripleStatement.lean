import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ProperTriple
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FourierJacobiAverage
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_compact_preimage_embX_mul_colE : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] (c ρ : ℕ) (_ : 1 ≤ ρ) (_ : ρ < c) (C : Set (GL (n ⊕ Fin c) k)) (_ : IsCompact C), ∃ D : Set (GL n k × N k n c (ρ + 1) × (n → k)), IsCompact D ∧ ∀ z : GL n k × N k n c (ρ + 1) × (n → k), embX c z.1 * (z.2.1 : GL (n ⊕ Fin c) k) * colE c (ρ + 1) z.2.2 ∈ C → z ∈ D := by
  first | exact @GlobalTheory.RootEx.ProperTriple.proper_triple | exact GlobalTheory.RootEx.ProperTriple.proper_triple | (intros; apply GlobalTheory.RootEx.ProperTriple.proper_triple <;> assumption)
