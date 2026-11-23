import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyExhaustion.PeelDefs
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.PropsCos
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.ProdIrrFiniteLength

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult

namespace PositivityTheory.Exh

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def EmbL (x : IrrGL k) (l : List (IrrGL k)) : Prop :=
  ∃ hd : ∑ a, (l.get a).1 = x.1, ∃ f : x.rep.IntertwiningMap (prodIrr l.get hd), Function.Injective f

def SubqL (x : IrrGL k) (l : List (IrrGL k)) : Prop :=
  ∃ hd : ∑ a, (l.get a).1 = x.1, IsSubquotient x.rep (prodIrr l.get hd)

def up (Δ : Segment k) : Segment k := Segment.ofFirst Δ.first Δ.isCusp_first (Δ.len + 1) (Nat.succ_pos _)

variable (k)

def MidP : Prop := ∀ (x : IrrGL k) (A M B : List (IrrGL k)), EmbL x (A ++ M ++ B) → ∃ σ, SubqL σ M ∧ EmbL x (A ++ [σ] ++ B)

def RefineP : Prop := ∀ (x σ : IrrGL k) (A M B : List (IrrGL k)), EmbL σ M → EmbL x (A ++ [σ] ++ B) → EmbL x (A ++ M ++ B)

def SwapP : Prop := ∀ (x a b : IrrGL k) (A B : List (IrrGL k)) (Δ Γ : Segment k), IsLSeg Δ a.rep → IsLSeg Γ b.rep → ¬ Δ.Linked Γ →
  EmbL x (A ++ [a, b] ++ B) → EmbL x (A ++ [b, a] ++ B)

def CuspEmbP : Prop := ∀ x : IrrGL k, ∃ l : List (IrrGL k), (∀ ρ ∈ l, ρ.IsCusp) ∧ EmbL x l

def SuppP : Prop := ∀ (x a y : IrrGL k) (l : List (IrrGL k)) (𝔫 : Multiset (Segment k)), (∀ ρ ∈ l, ρ.IsCusp) → EmbL x l →
  EmbL x [a, y] → IsL 𝔫 y.rep → ∀ Δ ∈ 𝔫, Δ.first ∈ l

def JuxtP : Prop := ∀ (σ b : IrrGL k) (Δ : Segment k), IsLSeg Δ b.rep → SubqL σ [Δ.first.nu ((Δ.len : ℕ) : ℂ), b] →
  IsLSeg (up Δ) σ.rep ∨ EmbL σ [b, Δ.first.nu ((Δ.len : ℕ) : ℂ)]

def LinkP : Prop := ∀ (ρ : IrrGL k) (hρ : ρ.IsCusp) (Δ : Segment k), (Segment.single ρ hρ).Linked Δ →
  Δ.first = ρ.nu 1 ∨ ρ = Δ.first.nu ((Δ.len : ℕ) : ℂ)

def MinP : Prop := ∀ l : List (IrrGL k), l ≠ [] → (∀ ρ ∈ l, ρ.IsCusp) →
  ∃ ρ ∈ l, ∀ ρ' ∈ l, ∀ j : ℕ, 0 < j → ρ ≠ ρ'.nu (j : ℕ)

end PositivityTheory.Exh

end
