import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel

namespace GlobalTheory.Published

def DepthZeroInduction : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k]
    (x : IrrGL k) (s : Multiset (IrrGL k)), HasSupport x.rep s →
    (∀ y ∈ s, fixed y.rep (KOne k (Fin y.1)) ≠ ⊥) → fixed x.rep (KOne k (Fin x.1)) ≠ ⊥

end GlobalTheory.Published

end
