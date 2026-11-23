import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.ColMatMulGlEmbMat
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.LSegJacquet
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GenericUnlinkedGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsExhaustionGL

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.SplitWeil

namespace GlobalTheory.BZSeg

section Props

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def GenericProdIff : Prop :=
  ∀ (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) (X : Fin h → Type) [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)]
    (π : ∀ a, Representation ℂ (GL (Fin (d a)) k) (X a)), (∀ a, IsSmooth (π a)) →
    (IsGeneric (multiProd (stdBlocks d hd) π) ↔ ∀ a, IsGeneric (π a))

def WhitRankProd2 : Prop :=
  ∀ (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (N : ℕ) (d : Fin 2 → ℕ) (hd : ∑ a, d a = N) (X : Fin 2 → Type)
    [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (π : ∀ a, Representation ℂ (GL (Fin (d a)) k) (X a)),
    (∀ a, IsSmooth (π a)) →
    Module.rank ℂ (TwJacquet (multiProd (stdBlocks d hd) π) (unipB k (Fin N)) (whitChar ψ N)) =
      Module.rank ℂ (TwJacquet (π 0) (unipB k (Fin (d 0))) (whitChar ψ (d 0))) *
        Module.rank ℂ (TwJacquet (π 1) (unipB k (Fin (d 1))) (whitChar ψ (d 1)))

def WhitRankIrr : Prop :=
  ∀ (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → π.IsIrreducible →
    Module.rank ℂ (TwJacquet π (unipB k (Fin N)) (whitChar ψ N)) ≤ 1

def CuspGeneric : Prop :=
  ∀ (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), 0 < N → IsSmooth π →
    π.IsIrreducible → IsCuspidal π → IsGeneric π

def LSegGeneric : Prop :=
  ∀ (Δ : Segment k) (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V),
    IsLSeg Δ π → IsGeneric π

def WhitRankTwoSeg : Prop :=
  ∀ (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (Δ Δ' : Segment k) (x y : IrrGL k) (N : ℕ)
    (hd : ∑ a, (![x, y] a).1 = N), IsLSeg Δ x.rep → IsLSeg Δ' y.rep →
    Module.rank ℂ (TwJacquet (prodIrr ![x, y] hd) (unipB k (Fin N)) (whitChar ψ N)) ≤ 1

def TwoSegGenericSub : Prop :=
  ∀ (Δ Δ' : Segment k) (x y : IrrGL k) (N : ℕ) (hd : ∑ a, (![x, y] a).1 = N), Δ'.Precedes Δ → IsLSeg Δ x.rep →
    IsLSeg Δ' y.rep → ∃ (W : Type) (_ : AddCommGroup W) (_ : Module ℂ W) (σ : Representation ℂ (GL (Fin N) k) W)
      (f : σ.IntertwiningMap (prodIrr ![x, y] hd)), Function.Injective f ∧ ¬ Function.Surjective f ∧ IsGeneric σ

def TwoSegNonGenQuot : Prop :=
  ∀ (Δ Δ' : Segment k) (x y : IrrGL k) (N : ℕ) (hd : ∑ a, (![x, y] a).1 = N), Δ'.Precedes Δ → IsLSeg Δ x.rep →
    IsLSeg Δ' y.rep → ∃ (W : Type) (_ : AddCommGroup W) (_ : Module ℂ W) (τ : Representation ℂ (GL (Fin N) k) W)
      (f : (prodIrr ![x, y] hd).IntertwiningMap τ), Function.Surjective f ∧ Nontrivial W ∧ ¬ IsGeneric τ

def AdjQuot : Prop :=
  ∀ (h N : ℕ) (Δ : Fin h → Segment k) (x : Fin h → IrrGL k) (hd : ∑ a, (x a).1 = N) (j : ℕ) (hj : j + 1 < h),
    (∀ i, IsLSeg (Δ i) (x i).rep) → (Δ ⟨j + 1, hj⟩).Precedes (Δ ⟨j, by omega⟩) →
    ∃ (W : Type) (_ : AddCommGroup W) (_ : Module ℂ W) (τ : Representation ℂ (GL (Fin N) k) W)
      (f : (prodIrr x hd).IntertwiningMap τ), Function.Surjective f ∧ Nontrivial W ∧ ¬ IsGeneric τ

def Reorder : Prop :=
  ∀ (h N : ℕ) (Δ : Fin h → Segment k) (x : Fin h → IrrGL k) (hd : ∑ a, (x a).1 = N), (∀ i, IsLSeg (Δ i) (x i).rep) →
    (∀ i j, i < j → ¬ (Δ i).Precedes (Δ j)) → (∃ i j, (Δ i).Linked (Δ j)) →
    ∃ (σ : Equiv.Perm (Fin h)) (j : ℕ) (hj : j + 1 < h), (Δ (σ ⟨j + 1, hj⟩)).Precedes (Δ (σ ⟨j, by omega⟩)) ∧
      ∀ hd' : ∑ a, (x (σ a)).1 = N, Nonempty ((prodIrr x hd).Equiv (prodIrr (x ∘ σ) hd'))

def ProdIrrFiniteLength : Prop :=
  ∀ (h N : ℕ) (x : Fin h → IrrGL k) (hd : ∑ a, (x a).1 = N), HasFiniteLength (prodIrr x hd)

def SwapProd : Prop :=
  ∀ (h N : ℕ) (x : Fin h → IrrGL k) (hd : ∑ a, (x a).1 = N) (j : ℕ) (hj : j + 1 < h) (M : ℕ)
    (hd2 : ∑ a, (![x ⟨j, by omega⟩, x ⟨j + 1, hj⟩] a).1 = M) (hd2' : ∑ a, (![x ⟨j + 1, hj⟩, x ⟨j, by omega⟩] a).1 = M)
    (hd' : ∑ a, (x (Equiv.swap ⟨j, by omega⟩ ⟨j + 1, hj⟩ a)).1 = N),
    Nonempty ((prodIrr ![x ⟨j, by omega⟩, x ⟨j + 1, hj⟩] hd2).Equiv (prodIrr ![x ⟨j + 1, hj⟩, x ⟨j, by omega⟩] hd2')) →
    Nonempty ((prodIrr x hd).Equiv (prodIrr (fun a => x (Equiv.swap ⟨j, by omega⟩ ⟨j + 1, hj⟩ a)) hd'))

def GCU : Prop :=
  ∀ (𝔪 : Multiset (Segment k)) (h N : ℕ) (Δ : Fin h → Segment k) (x : Fin h → IrrGL k) (hd : ∑ a, (x a).1 = N)
    (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsOrderedForm Δ 𝔪 →
    (∀ i, IsLSeg (Δ i) (x i).rep) → IsCosocle π (prodIrr x hd) → IsGeneric π → ∀ i j, ¬ (Δ i).Linked (Δ j)

def LUnlinkedIrr : Prop :=
  ∀ (h N : ℕ) (Δ : Fin h → Segment k) (x : Fin h → IrrGL k) (hd : ∑ a, (x a).1 = N),
    (∀ i j, ¬ (Δ i).Linked (Δ j)) → (∀ i, IsLSeg (Δ i) (x i).rep) → (prodIrr x hd).IsIrreducible

def LUnlinkedComm : Prop :=
  ∀ (Δ Δ' : Segment k) (x y : IrrGL k) (N : ℕ) (hd : ∑ a, (![x, y] a).1 = N) (hd' : ∑ a, (![y, x] a).1 = N),
    ¬ Δ.Linked Δ' → IsLSeg Δ x.rep → IsLSeg Δ' y.rep → Nonempty ((prodIrr ![x, y] hd).Equiv (prodIrr ![y, x] hd'))

end Props

end GlobalTheory.BZSeg

end
