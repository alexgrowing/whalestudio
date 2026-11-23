import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.HeckeCharacterParameters
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SameBlockOfPosC
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct

namespace GlobalTheory

theorem normSq_hcParam_sub_rhoSq (p q n : ℕ) (ap : Fin p → ℕ) (am : Fin q → ℕ) :
    normSq (hcParam n ap am) - rhoSq (p + q) = (∑ a, wtK n ap am a ^ 2 + ∑ i : Fin p, wtK n ap am (Sum.inl i) * ((p : ℚ) - q - 1 - 2 * (i : ℕ)) + ∑ j : Fin q, wtK n ap am (Sum.inr j) * ((p : ℚ) + q - 1 - 2 * (j : ℕ))) := by
  have hr : rhoSq (p + q) = ∑ i : Fin p, (((p : ℚ) - q - 1) / 2 - (i : ℕ)) ^ 2
      + ∑ j : Fin q, (((p : ℚ) + q - 1) / 2 - (j : ℕ)) ^ 2 := by
    unfold rhoSq
    rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => (((p : ℚ) - q - 1) / 2 - (i : ℕ)) ^ 2) p,
      Fin.sum_univ_eq_sum_range (fun i : ℕ => (((p : ℚ) + q - 1) / 2 - (i : ℕ)) ^ 2) q,
      Nat.add_comm p q, Finset.sum_range_add, add_comm]
    congr 1 <;> refine Finset.sum_congr rfl fun i _ => ?_ <;> push_cast <;> ring
  rw [hr]
  unfold normSq
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  have h1 : ∑ i : Fin p, hcParam n ap am (Sum.inl i) ^ 2
      = ∑ i : Fin p, wtK n ap am (Sum.inl i) ^ 2
        + ∑ i : Fin p, wtK n ap am (Sum.inl i) * ((p : ℚ) - q - 1 - 2 * (i : ℕ))
        + ∑ i : Fin p, (((p : ℚ) - q - 1) / 2 - (i : ℕ)) ^ 2 := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hcParam, wtK]
    ring
  have h2 : ∑ j : Fin q, hcParam n ap am (Sum.inr j) ^ 2
      = ∑ j : Fin q, wtK n ap am (Sum.inr j) ^ 2
        + ∑ j : Fin q, wtK n ap am (Sum.inr j) * ((p : ℚ) + q - 1 - 2 * (j : ℕ))
        + ∑ j : Fin q, (((p : ℚ) + q - 1) / 2 - (j : ℕ)) ^ 2 := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hcParam, wtK]
    ring
  rw [h1, h2]
  ring

end GlobalTheory
