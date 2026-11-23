import Mathlib
import Formalism.SharpRestriction.ParConsts
import Formalism.LocalRingCardinality.DataKerI
import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
open Formalism.MainNotions Formalism.BasicNotions Formalism.MainNotions.G Classical

namespace GlobalTheory

theorem youngDiagram_card_eq_sum_rowLen_range (μ : YoungDiagram) (n : ℕ) (h : μ.colLen 0 ≤ n) :
    μ.card = ∑ r ∈ Finset.range n, μ.rowLen r := by
  have hmap : ∀ c ∈ μ.cells, c.1 ∈ Finset.range n := by
    intro c hc
    rw [Finset.mem_range]
    have h1 : (c.1, c.2) ∈ μ := hc
    have h2 : (c.1, 0) ∈ μ := μ.up_left_mem le_rfl (Nat.zero_le _) h1
    exact lt_of_lt_of_le (YoungDiagram.mem_iff_lt_colLen.1 h2) h
  unfold YoungDiagram.card
  rw [Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (fun c hc => hmap c hc)]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [YoungDiagram.rowLen_eq_card]
  rfl

theorem nuD_card_eq_sum_nuRow : ∀ (D : D7), NuRowOK D → ∀ (u : D.what₂.Word), ∀ j < D.R.m, ∀ (z : Bool × HH D), (((nuD D u j z).card : ℕ) : ℝ) = ∑ r ∈ Finset.range (D.R.N j), DV.nuRow D u (j + 1) (tauPl D z) r := by
  intro D hD u j hj z
  rw [youngDiagram_card_eq_sum_rowLen_range _ _ (nuD_rows D u j z), Nat.cast_sum]
  refine Finset.sum_congr rfl fun r hr => ?_
  rw [hD u j hj z r, if_pos (Finset.mem_range.1 hr)]

end GlobalTheory
