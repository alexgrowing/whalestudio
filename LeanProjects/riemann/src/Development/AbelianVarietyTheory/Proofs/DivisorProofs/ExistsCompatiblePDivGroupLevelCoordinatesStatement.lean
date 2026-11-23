import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompatiblePDivGroupLevelCoordinates
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DUnitMemRangeOfMemKerIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowEqOfIntegers
open GlobalTheory GlobalTheory.PDivGroup
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_compatible_pDivGroup_level_coordinates : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ G : PDivGroup p O, ∃ (d : ℕ) (x : ∀ n, Fin d → G.A n), (∀ n i, Coalgebra.counit (R := O) (x n i) = 0) ∧ (∀ n i, G.res n (x (n + 1) i) = x n i) ∧ (∀ n, Submodule.span O (Set.range fun i => PDiv.dUnit O (x n i)) = ⊤) ∧ ∀ n, ∃ l : Fin d → (PDiv.Cot O (G.A n) →ₗ[O] O ⧸ Ideal.span {(p : O) ^ n}), ∀ i j, l i (PDiv.dUnit O (x n j)) = if i = j then 1 else 0 := by
  first | exact @GlobalTheory.PDiv.exists_compatible_coordinates | exact GlobalTheory.PDiv.exists_compatible_coordinates | (intros; apply GlobalTheory.PDiv.exists_compatible_coordinates <;> assumption)
