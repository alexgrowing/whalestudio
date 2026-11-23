import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd

open NumberField MeasureTheory

namespace GlobalTheory.IndefiniteRowSideFullHecke.DefiniteFiniteCount

open Formalism.MainNotions.S GlobalTheory.Count

def DefiniteHyp (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (p : ℕ) : Prop :=
  IsDSData B d ∧ SigIs B p 0 ∧ 1 ≤ p ∧ 1 ≤ B.g ∧ B.g₀.Prime ∧ 4 * B.I.n < B.g₀ ∧
    (Ideal.primesOver (Ideal.span {(B.g₀ : ℤ)}) (𝓞 B.I.E)).ncard = Module.finrank ℚ B.I.E

def DefiniteCount : Prop :=
  ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (p : ℕ), DefiniteHyp B d p →
    (B.D : ℝ) = mainTerm B d

def DefiniteCountFin : Prop :=
  ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (p : ℕ), DefiniteHyp B d p →
    FiniteDimensional ℂ (B.I.eHom B.σs B.μf B.fund B.R B.Re) ∧
      B.I.muA B.μf B.fund ≠ ⊤ ∧ (B.D : ℝ) = mainTerm B d

theorem DefiniteHyp.rank_eq {B : RowsAut} {d : InfinitePlace B.I.F → ℝ} {p : ℕ}
    (h : DefiniteHyp B d p) : B.I.n = p := by
  obtain ⟨v⟩ : Nonempty (InfinitePlace B.I.F) := inferInstance
  obtain ⟨hp, hq⟩ := h.2.1 v
  unfold AutInst.pAt at hp
  unfold AutInst.qAt at hq
  have hall : ∀ a, B.I.ε v a = true := by
    intro a
    by_contra ha
    have hm : a ∈ (Finset.univ.filter fun a => B.I.ε v a = false) := by
      simpa using ha
    rw [Finset.card_eq_zero.mp hq] at hm
    simp at hm
  rw [← hp, Finset.filter_true_of_mem fun a _ => hall a]
  simp

end GlobalTheory.IndefiniteRowSideFullHecke.DefiniteFiniteCount
