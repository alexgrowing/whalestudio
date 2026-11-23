import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsComplementaryProductOfIsCuspidal

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel MeasureTheory

namespace GlobalTheory.Published

def GenericUnlinkedGL : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k]
    (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V),
    IsSmooth π → π.IsIrreducible → IsGeneric π →
    ∃ (h : ℕ) (Δ : Fin h → Segment k) (x : Fin h → IrrGL k) (hd : ∑ a, (x a).1 = N),
      (∀ i j, i ≠ j → ¬ (Δ i).Linked (Δ j)) ∧ (∀ i, IsLSeg (Δ i) (x i).rep) ∧ Nonempty (π.Equiv (prodIrr x hd))

end GlobalTheory.Published

end
