import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.CuspStdSubGeneric
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.LSegJacquet

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.SplitWeil

namespace GlobalTheory.BZSeg

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def NuPair : Prop :=
  ∀ (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ω : Representation ℂ (GL (Fin N) k) V), IsSmooth ω →
    ω.IsIrreducible → ¬ IsGeneric ω → ∃ (α β β' : IrrGL k) (hd : ∑ a, (![α, β] a).1 = N)
      (hd' : ∑ a, (![β', α.nu 1] a).1 = N), 0 < α.1 ∧ 0 < β.1 ∧ β'.1 = β.1 ∧ 1 ≤ Zc.jm ![α, β] hd ω ∧
        1 ≤ Zc.jm ![β', α.nu 1] hd' ω

def CuspPairSubGeneric : Prop :=
  ∀ (x y : IrrGL k) (N : ℕ) (hd : ∑ a, (![x, y] a).1 = N), x.IsCusp → y.IsCusp → y ≠ x.nu 1 →
    ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GL (Fin N) k) W)
      (f : σ.IntertwiningMap (prodIrr ![x, y] hd)), Function.Injective f → Nontrivial W → IsGeneric σ

end GlobalTheory.BZSeg

end
