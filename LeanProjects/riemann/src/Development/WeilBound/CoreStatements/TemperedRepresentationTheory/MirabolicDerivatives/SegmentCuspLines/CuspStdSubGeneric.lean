import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.CuspLinesIrr

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.SplitWeil

namespace GlobalTheory.BZSeg

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def StdSubGeneric : Prop :=
  ∀ (h N : ℕ) (Δ : Fin h → Segment k) (x : Fin h → IrrGL k) (hd : ∑ a, (x a).1 = N), (∀ i, IsLSeg (Δ i) (x i).rep) →
    (∀ i j, i < j → ¬ (Δ i).Precedes (Δ j)) → ∀ (W : Type) [AddCommGroup W] [Module ℂ W]
    (σ : Representation ℂ (GL (Fin N) k) W) (f : σ.IntertwiningMap (prodIrr x hd)), Function.Injective f → Nontrivial W →
    IsGeneric σ

def StdQuotGeneric : Prop :=
  ∀ (h N : ℕ) (Δ : Fin h → Segment k) (x : Fin h → IrrGL k) (hd : ∑ a, (x a).1 = N), (∀ i, IsLSeg (Δ i) (x i).rep) →
    (∀ i j, i < j → ¬ (Δ j).Precedes (Δ i)) → ∀ (W : Type) [AddCommGroup W] [Module ℂ W]
    (τ : Representation ℂ (GL (Fin N) k) W) (f : (prodIrr x hd).IntertwiningMap τ), Function.Surjective f → Nontrivial W →
    IsGeneric τ

def CuspStdSubGeneric : Prop :=
  ∀ (r N : ℕ) (x : Fin r → IrrGL k) (hd : ∑ a, (x a).1 = N), (∀ i, (x i).IsCusp) → (∀ i j, i < j → x j ≠ (x i).nu 1) →
    ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GL (Fin N) k) W)
      (f : σ.IntertwiningMap (prodIrr x hd)), Function.Injective f → Nontrivial W → IsGeneric σ

def WhitRankStd : Prop :=
  ∀ (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (h N : ℕ) (x : Fin h → IrrGL k) (hd : ∑ a, (x a).1 = N),
    Module.rank ℂ (TwJacquet (prodIrr x hd) (unipB k (Fin N)) (whitChar ψ N)) ≤ 1

def TwoSegReducible : Prop :=
  ∀ (Δ Δ' : Segment k) (x y : IrrGL k) (N : ℕ) (hd : ∑ a, (![x, y] a).1 = N), Δ.Linked Δ' → IsLSeg Δ x.rep →
    IsLSeg Δ' y.rep → ¬ (prodIrr ![x, y] hd).IsIrreducible

end GlobalTheory.BZSeg

end
