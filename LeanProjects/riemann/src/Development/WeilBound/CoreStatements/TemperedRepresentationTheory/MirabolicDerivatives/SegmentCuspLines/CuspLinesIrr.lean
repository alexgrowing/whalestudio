import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.ProdIrrFiniteLength

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.SplitWeil

namespace GlobalTheory.BZSeg

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def CuspPairIrr : Prop :=
  ∀ (x y : IrrGL k) (N : ℕ) (hd : ∑ a, (![x, y] a).1 = N), x.IsCusp → y.IsCusp → y ≠ x.nu 1 → x ≠ y.nu 1 →
    (prodIrr ![x, y] hd).IsIrreducible

def CuspLinesIrr : Prop :=
  ∀ (x y : IrrGL k) (N : ℕ) (hd : ∑ a, (![x, y] a).1 = N), x.IsCusp → y.IsCusp → ¬ IrrGL.Inert x y →
    (prodIrr ![x, y] hd).IsIrreducible

end GlobalTheory.BZSeg

end
