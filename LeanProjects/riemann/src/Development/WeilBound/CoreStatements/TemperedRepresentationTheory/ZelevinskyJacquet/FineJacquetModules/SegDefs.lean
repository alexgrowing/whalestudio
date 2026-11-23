import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.LSegJacquet

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult

namespace Zc.Seg

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def dec (Δ : Segment k) : Fin Δ.len → IrrGL k := fun a => Δ.term (Fin.rev a)

def concat {s : ℕ} (c : Fin s → ℕ) (x : ∀ a, Fin (c a) → IrrGL k) : Fin (∑ a, c a) → IrrGL k :=
  fun i => x (finSigmaFinEquiv.symm i).1 (finSigmaFinEquiv.symm i).2

def FineJac (Δ : Segment k) : Prop :=
  ∀ {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsLSeg Δ π →
    (∀ hd : ∑ a, (dec Δ a).1 = N, jm (dec Δ) hd π = 1) ∧
    ∀ (c : ℕ) (y : Fin c → IrrGL k) (hy : ∑ a, (y a).1 = N), (∀ a, (y a).IsCusp) → 1 ≤ jm y hy π →
      ∃ h : c = Δ.len, ∀ a, y a = dec Δ (Fin.cast h a)

end Zc.Seg

end
