import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.LSegJacquet
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.PropsCos
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyInterleaving.Interleave

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult

namespace Zc.M

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def decW (Δ : Segment k) : List (IrrGL k) := List.ofFn fun i : Fin Δ.len => Δ.term (Fin.rev i)

def wtW {h : ℕ} (Δ : Fin h → Segment k) : List (IrrGL k) :=
  (List.ofFn fun i : Fin h => decW (Δ (Fin.rev i))).flatten

def Wd {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V)
    (w : List (IrrGL k)) : Prop :=
  ∃ hd : ∑ a, (w.get a).1 = N, jm w.get hd π ≠ 0

def InShW (𝔪 : Multiset (Segment k)) (w : List (IrrGL k)) : Prop :=
  ∃ L : List (Segment k), (L : Multiset (Segment k)) = 𝔪 ∧ Comb.Shuffle (L.map decW) w

abbrev CuspT (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] : Type 1 :=
  {x : IrrGL k // x.IsCusp}

def sNu (x : CuspT k) : CuspT k := ⟨x.1.nu 1, x.2.nu 1⟩

def toA (Δ : Segment k) : Comb.ASeg (CuspT k) := ⟨⟨Δ.first, Δ.isCusp_first⟩, Δ.len, Δ.len_pos⟩

def LInjective (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] : Prop :=
  ∀ (𝔪 𝔫 : Multiset (Segment k)) (x : IrrGL k), IsL 𝔪 x.rep → IsL 𝔫 x.rep → 𝔪 = 𝔫

end Zc.M

end
