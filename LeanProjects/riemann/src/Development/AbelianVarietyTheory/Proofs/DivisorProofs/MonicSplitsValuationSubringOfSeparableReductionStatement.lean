import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MonicSplitsValuationSubringOfSeparableReduction
import Mathlib
open Polynomial IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.monic_splits_valuationSubring_of_separable_reduction : ∀ (Ω : Type) [Field Ω] [IsSepClosed Ω] (V : ValuationSubring Ω) (q : Polynomial V), q.Monic → (q.map (IsLocalRing.residue V)).Separable → ∃ s : Multiset V, q = (s.map fun b => Polynomial.X - Polynomial.C b).prod := by
  first | exact @GlobalTheory.monic_splits_of_separable_residue | exact GlobalTheory.monic_splits_of_separable_residue | (intros; apply GlobalTheory.monic_splits_of_separable_residue <;> assumption)
