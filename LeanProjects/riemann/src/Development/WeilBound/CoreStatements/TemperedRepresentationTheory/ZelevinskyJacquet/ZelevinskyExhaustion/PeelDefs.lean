import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyExhaustion.PropsExh

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult

namespace Zc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def Peel (Δ : Segment k) (x : IrrGL k) : Prop :=
  ∃ (y : Fin 2 → IrrGL k) (hd : ∑ a, (y a).1 = x.1), IsLSeg Δ (y 0).rep ∧
    ∃ f : x.rep.IntertwiningMap (prodIrr y hd), Function.Injective f

def BeginsBelow (Γ Δ : Segment k) : Prop := ∃ j : ℕ, 0 < j ∧ Δ.first = Γ.first.nu j

def Far (Δ Γ : Segment k) : Prop :=
  ∀ (a : Fin Δ.len) (b : Fin Γ.len) (j : ℤ), |j| ≤ 1 → Δ.term a ≠ (Γ.term b).nu (j : ℂ)

variable (k) in

def PeelMinP : Prop :=
  ∀ x : IrrGL k, 0 < x.1 → ∃ Δ : Segment k, Peel Δ x ∧ ∀ Δ' : Segment k, Peel Δ' x → ¬ BeginsBelow Δ' Δ

variable (k) in

def PeelDescendP : Prop :=
  ∀ (x : IrrGL k) (y : Fin 2 → IrrGL k) (hd : ∑ a, (y a).1 = x.1) (Δ : Segment k) (𝔫 : Multiset (Segment k)),
    IsLSeg Δ (y 0).rep → IsL 𝔫 (y 1).rep → (∃ f : x.rep.IntertwiningMap (prodIrr y hd), Function.Injective f) →
    (∃ Δ' ∈ 𝔫, Δ'.Precedes Δ) → ∃ Γ : Segment k, Peel Γ x ∧ BeginsBelow Γ Δ

variable (k) in

def PeelGoodP : Prop :=
  ∀ (x : IrrGL k) (y : Fin 2 → IrrGL k) (hd : ∑ a, (y a).1 = x.1) (Δ : Segment k) (𝔫 : Multiset (Segment k)),
    IsLSeg Δ (y 0).rep → IsL 𝔫 (y 1).rep → (∃ f : x.rep.IntertwiningMap (prodIrr y hd), Function.Injective f) →
    (∀ Δ' ∈ 𝔫, ¬ Δ'.Precedes Δ) → IsL (𝔫 + {Δ}) x.rep

end Zc

end
