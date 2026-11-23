import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanCriterion.Zj
import GroundTheory.AutomorphicForms.SupercuspidalCoefficients

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult

namespace GlobalTheory.CompanionTheory.BlockIndex

theorem sum_castLE_eq_range {h : ℕ} (d : Fin h → ℕ) (a : Fin h) :
    ∑ b : Fin a, d (Fin.castLE a.2.le b) =
      ∑ c ∈ Finset.range a, (fun c => if hc : c < h then d ⟨c, hc⟩ else 0) c := by
  rw [← Fin.sum_univ_eq_sum_range (fun c => if hc : c < h then d ⟨c, hc⟩ else 0) a]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [dif_pos (b.2.trans a.2)] <;> rfl

theorem partial_sum_succ_le {h : ℕ} (d : Fin h → ℕ) {a b : Fin h} (hab : b < a) :
    ∑ c : Fin b, d (Fin.castLE b.2.le c) + d b ≤ ∑ c : Fin a, d (Fin.castLE a.2.le c) := by
  have hsub : Finset.range ((b : ℕ) + 1) ⊆ Finset.range a := fun x hx =>
    Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hx) (show (b : ℕ) + 1 ≤ a from hab))
  have key := Finset.sum_le_sum_of_subset (f := fun c => if hc : c < h then d ⟨c, hc⟩ else 0) hsub
  rw [Finset.sum_range_succ, dif_pos b.2] at key
  rw [GlobalTheory.CompanionTheory.BlockIndex.sum_castLE_eq_range d b, GlobalTheory.CompanionTheory.BlockIndex.sum_castLE_eq_range d a]
  exact key

theorem stdBlocks_lt_of_lt {h N : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N) {a b : Fin h} (hab : b < a)
    (x : Fin (d a)) (y : Fin (d b)) : stdBlocks d hd ⟨b, y⟩ < stdBlocks d hd ⟨a, x⟩ := by
  rw [Fin.lt_def, GlobalTheory.SmGL.stdBlocks_val,
    GlobalTheory.SmGL.stdBlocks_val]
  have h1 := GlobalTheory.CompanionTheory.BlockIndex.partial_sum_succ_le d hab
  have h2 := y.2
  omega

theorem blockIdx_monotone : ∀ (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N), Monotone (Zl.JC.blockIdx d hd) := by
  intro h N d hd i j hij
  by_contra H
  rw [not_le] at H
  have H' : ((GlobalTheory.SmGL.stdBlocks d hd).symm j).1 <
      ((GlobalTheory.SmGL.stdBlocks d hd).symm i).1 := H
  have key := GlobalTheory.CompanionTheory.BlockIndex.stdBlocks_lt_of_lt d hd H'
    ((GlobalTheory.SmGL.stdBlocks d hd).symm i).2
    ((GlobalTheory.SmGL.stdBlocks d hd).symm j).2
  simp only [Sigma.eta, Equiv.apply_symm_apply] at key
  exact absurd hij (not_le.mpr key)

end GlobalTheory.CompanionTheory.BlockIndex
