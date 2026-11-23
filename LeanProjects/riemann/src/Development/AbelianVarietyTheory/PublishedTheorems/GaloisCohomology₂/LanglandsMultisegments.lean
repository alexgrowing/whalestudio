import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsComplementaryProductOfIsCuspidal

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel MeasureTheory

namespace GlobalTheory.Published

def LanglandsMultisegments : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k],
    (∀ (𝔪 𝔫 : Multiset (Segment k)) (x : IrrGL k), IsL 𝔪 x.rep → IsL 𝔫 x.rep → 𝔪 = 𝔫) ∧
    ∀ (𝔪 𝔫 : Multiset (Segment k)) (x : Fin 2 → IrrGL k) (y : IrrGL k) (hd : ∑ a, (x a).1 = y.1),
      IsL 𝔪 (x 0).rep → IsL 𝔫 (x 1).rep → IsL (𝔪 + 𝔫) y.rep → IsSubquotient y.rep (prodIrr x hd)

end GlobalTheory.Published

end
