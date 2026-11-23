import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.LSegJacquet

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult

namespace Zc

def JacquetSubLeft (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] : Prop :=
  ∀ x : IrrGL k, 0 < x.1 → ∃ (y : Fin 2 → IrrGL k) (hd : ∑ a, (y a).1 = x.1), (y 0).IsCusp ∧
    ∃ f : x.rep.IntertwiningMap (prodIrr y hd), Function.Injective f

def SocleL (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] : Prop :=
  ∀ (x : IrrGL k) (y : Fin 2 → IrrGL k) (hd : ∑ a, (y a).1 = x.1), (y 0).IsCusp →
    (∃ 𝔫 : Multiset (Segment k), IsL 𝔫 (y 1).rep) →
    (∃ f : x.rep.IntertwiningMap (prodIrr y hd), Function.Injective f) → ∃ 𝔪 : Multiset (Segment k), IsL 𝔪 x.rep

end Zc

end
